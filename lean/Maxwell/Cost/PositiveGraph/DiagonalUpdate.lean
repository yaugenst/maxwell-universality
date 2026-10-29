import Maxwell.Cost.PositiveGraph.DiagonalWord
import Maxwell.Cost.BankArray.ReadBank
import Maxwell.Cost.BankArray.Write
import Maxwell.Cost.WordCall

namespace Maxwell.Cost.PositiveGraph.DiagonalUpdate
open Structured
open RationalAccumulator (Blank)
set_option maxHeartbeats 1200000

def payload (value : ℕ) (negative half mediator : Bool) : List Bool :=
  FixedWidth.bits 4 (DiagonalWord.updated value negative half mediator).bits

def code (indexBank : ℕ) : Code := .seq (BankArray.readBankCode 147 indexBank 145 148 120)
  (.seq (.call DiagonalWord.program)
    (.seq (BankArray.writeCode 147 indexBank 145 120) (.call (TapeOps.clear 120))))

def costCap (index : List Bool) (base : ℕ) (clock : List Bool) (value : ℕ)
    (negative half mediator : Bool) : ℕ :=
  BankArray.costCap (4 : ℕ).bits index base.bits clock+
    BankArray.costCap (4 : ℕ).bits index base.bits (payload value negative half mediator)+200

structure Frame (s t : BitRAMState) : Prop where
  inputHead : t.inputHead = s.inputHead
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ i, (i = 4 ∨ 10 ≤ i) → i ≠ 120 → t.tapes i = s.tapes i
  registers : ∀ i, 15 ≤ i → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 28 → i ≠ 29 →
    (i < 50 ∨ 55 < i) → t.registers i = s.registers i

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u :=
  ⟨k.inputHead.trans h.inputHead,k.randomCursor.trans h.randomCursor,k.output.trans h.output,
    fun i hi hj => (k.tapes i hi hj).trans (h.tapes i hi hj),
    fun i hi a b c d e f g => (k.registers i hi a b c d e f g).trans (h.registers i hi a b c d e f g)⟩

private theorem scratch_of_tapes {s t : BitRAMState} (h : BankArray.Scratch s)
    (keep : ∀ i, i < 10 → t.tapes i = s.tapes i) : BankArray.Scratch t := by
  rcases h with ⟨h0,h1,h2,h3,h5,h6,h8,h9⟩
  exact ⟨RationalAccumulator.blank_of_eq (keep 0 (by omega)) h0,
    RationalAccumulator.blank_of_eq (keep 1 (by omega)) h1,
    RationalAccumulator.blank_of_eq (keep 2 (by omega)) h2,
    RationalAccumulator.blank_of_eq (keep 3 (by omega)) h3,
    RationalAccumulator.blank_of_eq (keep 5 (by omega)) h5,
    RationalAccumulator.blank_of_eq (keep 6 (by omega)) h6,
    RationalAccumulator.blank_of_eq (keep 8 (by omega)) h8,
    RationalAccumulator.blank_of_eq (keep 9 (by omega)) h9⟩

/-- An indexed diagonal update reads four physical cells, executes the fixed
Boolean carry/borrow circuit, writes those cells, and reclaims its payload. -/
theorem executes {n : ℕ} (indexBank : ℕ) (hbank : 10 ≤ indexBank) (hbank120 : indexBank ≠ 120)
    (input : List Bool) (tape : ℕ → Bool) (index clock : List Bool) (base value : ℕ)
    (words : Vector (List Bool) n) (i : Fin n) (hindex : addressValue index = i.val)
    (hclock : clock.length = 4) (hvalue : value < 16)
    (hword : words.get i = FixedWidth.bits 4 value.bits) (negative half mediator : Bool)
    (s : Store) (hscratch : BankArray.Scratch s.val) (h7 : Blank s.val 7) (h120 : Blank s.val 120)
    (h147 : BankArray.Word s.val 147 (4 : ℕ).bits) (hindexWord : BankArray.Word s.val indexBank index)
    (h145 : BankArray.Word s.val 145 base.bits) (h148 : BankArray.Word s.val 148 clock)
    (harray : BitArray.Represents s.val.memory base 4 words)
    (hnegative : s.val.registers 44 = negative) (hhalf : s.val.registers 45 = half)
    (hmediator : s.val.registers 47 = mediator) :
    ∃ steps, ∃ t : Store, steps ≤ costCap index base clock value negative half mediator ∧
      Executes input tape (code indexBank) steps s t ∧
      t.val.memory = MemoryWord.writeBits s.val.memory (base+4*i.val) (payload value negative half mediator) ∧
      BitArray.Represents t.val.memory base 4 (words.set i (payload value negative half mediator)) ∧
      BankArray.Scratch t.val ∧ Blank t.val 7 ∧ Blank t.val 120 ∧
      t.val.registers 44 = negative ∧ t.val.registers 45 = half ∧ t.val.registers 47 = mediator ∧ Frame s.val t.val := by
  obtain ⟨c1,a,hc1,ea,haw,has,ha7,ham,haa,fa⟩ := BankArray.read_bank 147 indexBank 145 148 120
    (by omega) hbank (by omega) (by omega) (by omega) input tape (4 : ℕ).bits index base.bits clock words i
    (by decide) hindex (by simpa only [RationalAccumulator.address_bits] using hclock) s hscratch h7 h120
    h147 hindexWord h145 h148 (by simpa only [RationalAccumulator.address_bits] using harray)
  obtain ⟨origin,haw⟩ := haw
  have flagA (j : ℕ) (hj : 40 ≤ j) : a.val.registers j = s.val.registers j :=
    fa.2.2.2.2 j (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨b,eb,hbw,hbn,hbh,hbm,fb⟩ := DiagonalWord.executes input tape a value hvalue origin negative half mediator
    (by simpa only [hword] using haw) ((flagA 44 (by omega)).trans hnegative)
    ((flagA 45 (by omega)).trans hhalf) ((flagA 47 (by omega)).trans hmediator)
  have hbs : BankArray.Scratch b.val := scratch_of_tapes has (fun j hj => fb.tapes j (by omega))
  have keepB (j : ℕ) (hj : 10 ≤ j) (h120 : j ≠ 120) : b.val.tapes j = s.val.tapes j :=
    (fb.tapes j h120).trans (fa.2.2.2.1 j (Or.inr hj) h120)
  have hba : BitArray.Represents b.val.memory base 4 words := by
    simpa only [fb.memory,RationalAccumulator.address_bits] using haa
  obtain ⟨c2,c,hc2,ec,hcm,hca,hcs,hc7,fc⟩ := BankArray.write_bank 147 indexBank 145 120
    (by omega) hbank (by omega) (by omega) input tape (4 : ℕ).bits index base.bits
    (payload value negative half mediator) words i (by decide) hindex
    (by simp only [payload,FixedWidth.bits_length,RationalAccumulator.address_bits]) b hbs
    (BankArray.word_of_eq (keepB 147 (by omega) (by omega)) h147)
    (BankArray.word_of_eq (keepB indexBank hbank hbank120) hindexWord)
    (BankArray.word_of_eq (keepB 145 (by omega) (by omega)) h145) ⟨origin,hbw⟩
    (by simpa only [RationalAccumulator.address_bits] using hba)
  have hcw : c.val.tapes 120 = BitTape.shifted (payload value negative half mediator) origin :=
    (fc.2.2.2.1 120 (Or.inr (by omega))).trans hbw
  obtain ⟨t,et,ht,ft⟩ := WordCall.clear 120 input tape (payload value negative half mediator) origin c hcw
  have keepT (j : ℕ) (hj : j ≠ 120) : t.val.tapes j = c.val.tapes j := by simp [ht,hj]
  have flagC (j : ℕ) (hj : 40 ≤ j) : c.val.registers j = b.val.registers j :=
    fc.2.2.2.2 j (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have flagT (j : ℕ) (hj : 40 ≤ j) : t.val.registers j = c.val.registers j :=
    ft.2.2.2.2.2.2 j (by omega) (by omega)
  refine ⟨c1+(DiagonalWord.cost half mediator+(c2+(6*(payload value negative half mediator).length+4))),t,
    ?_,ea.seq (eb.seq (ec.seq et)),?_,?_,scratch_of_tapes hcs (fun j hj => keepT j (by omega)),
    RationalAccumulator.blank_of_eq ((keepT 7 (by omega)).trans (hc7.trans (fb.tapes 7 (by omega)))) ha7,
    ⟨origin+(payload value negative half mediator).length,by simp [ht]⟩,
    (flagT 44 (by omega)).trans ((flagC 44 (by omega)).trans hbn),
    (flagT 45 (by omega)).trans ((flagC 45 (by omega)).trans hbh),
    (flagT 47 (by omega)).trans ((flagC 47 (by omega)).trans hbm),
    ⟨ft.2.1.trans (fc.1.trans (fb.inputHead.trans fa.1)),
      ft.2.2.2.1.trans (fc.2.1.trans (fb.randomCursor.trans fa.2.1)),
      ft.2.2.2.2.1.trans (fc.2.2.1.trans (fb.output.trans fa.2.2.1)),
      fun j hj hj120 => (keepT j hj120).trans ((fc.2.2.2.1 j hj).trans
        ((fb.tapes j hj120).trans (fa.2.2.2.1 j hj hj120))),
      fun j hj h24 h25 h26 h27 h28 h29 h50 => (ft.2.2.2.2.2.2 j h26 h27).trans
        ((fc.2.2.2.2 j hj h24 h25 h26 h27 h28 h29).trans ((fb.registers j h50).trans
          (fa.2.2.2.2 j hj h24 h25 h26 h27 h28 h29)))⟩⟩
  · have hc := DiagonalWord.cost_le half mediator
    simp only [RationalAccumulator.address_bits] at hc1
    simp only [payload,FixedWidth.bits_length]
    dsimp [costCap]
    omega
  · rw [ft.2.2.1,hcm,fb.memory,ham]
    simp only [RationalAccumulator.address_bits,Nat.mul_comm]
  · simpa only [ft.2.2.1,RationalAccumulator.address_bits] using hca

theorem compiled_run {n : ℕ} (indexBank : ℕ) (hbank : 10 ≤ indexBank) (hbank120 : indexBank ≠ 120)
    (input : List Bool) (tape : ℕ → Bool) (index clock : List Bool) (base value : ℕ)
    (words : Vector (List Bool) n) (i : Fin n) (hindex : addressValue index = i.val)
    (hclock : clock.length = 4) (hvalue : value < 16)
    (hword : words.get i = FixedWidth.bits 4 value.bits) (negative half mediator : Bool)
    (s : Store) (hscratch : BankArray.Scratch s.val) (h7 : Blank s.val 7) (h120 : Blank s.val 120)
    (h147 : BankArray.Word s.val 147 (4 : ℕ).bits) (hindexWord : BankArray.Word s.val indexBank index)
    (h145 : BankArray.Word s.val 145 base.bits) (h148 : BankArray.Word s.val 148 clock)
    (harray : BitArray.Represents s.val.memory base 4 words)
    (hnegative : s.val.registers 44 = negative) (hhalf : s.val.registers 45 = half)
    (hmediator : s.val.registers 47 = mediator) :
    ∃ t : Store,
      (runPriced ((code indexBank).compile.next input tape)
        (costCap index base clock value negative half mediator+1) s.val).finished = some (t.place (code indexBank).size) ∧
      (runPriced ((code indexBank).compile.next input tape)
        (costCap index base clock value negative half mediator+1) s.val).instructions ≤
          costCap index base clock value negative half mediator ∧
      t.val.memory = MemoryWord.writeBits s.val.memory (base+4*i.val) (payload value negative half mediator) ∧
      BitArray.Represents t.val.memory base 4 (words.set i (payload value negative half mediator)) ∧
      BankArray.Scratch t.val ∧ Blank t.val 7 ∧ Blank t.val 120 ∧
      t.val.registers 44 = negative ∧ t.val.registers 45 = half ∧ t.val.registers 47 = mediator ∧ Frame s.val t.val := by
  obtain ⟨steps,t,hcost,he,ht⟩ := executes indexBank hbank hbank120 input tape index clock base value words i
    hindex hclock hvalue hword negative half mediator s hscratch h7 h120 h147 hindexWord h145 h148
    harray hnegative hhalf hmediator
  have hr := he.compiled_run (costCap index base clock value negative half mediator+1) (by omega)
  exact ⟨t,hr.1,hr.2 ▸ hcost,ht⟩

end Maxwell.Cost.PositiveGraph.DiagonalUpdate
