import Maxwell.Cost.PowerOfTwo

namespace Maxwell.Cost.NormalizedRecordParser.Payload
open Structured

/-- The actual binary word `2^p` contains exactly `p` zero cells before its
one cell. It is a reusable clock for the fixed-width coefficient payload. -/
def program : BitRAM := ⟨[
  .readTape 82 26 27, .branch 26 8 2,
  .readTape 85 20 28, .writeTape 83 20,
  .tapeRight 83, .tapeRight 85, .tapeRight 82, .jump 0, .halt]⟩

def advance (s : BitRAMState) (b : Bool) : BitRAMState :=
  {s with
    pc := 0
    registers := Function.update (Function.update (Function.update
      (Function.update s.registers 26 false) 27 true) 20 b) 28 true
    tapes := Function.update (Function.update (Function.update s.tapes 83
      {(s.tapes 83).write (some b) with head := (s.tapes 83).head + 1}) 85
      {s.tapes 85 with head := (s.tapes 85).head + 1}) 82
      {s.tapes 82 with head := (s.tapes 82).head + 1}}

def finish (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 8
    registers := Function.update (Function.update s.registers 26 true) 27 true}

def Frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, i ≠ 82 → i ≠ 83 → i ≠ 85 → t.tapes i = s.tapes i) ∧
  (∀ i, i ≠ 20 → i ≠ 26 → i ≠ 27 → i ≠ 28 → t.registers i = s.registers i)

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u :=
  ⟨k.1.trans h.1, k.2.1.trans h.2.1, k.2.2.1.trans h.2.2.1,
    k.2.2.2.1.trans h.2.2.2.1, k.2.2.2.2.1.trans h.2.2.2.2.1,
    fun i h82 h83 h85 => (k.2.2.2.2.2.1 i h82 h83 h85).trans (h.2.2.2.2.2.1 i h82 h83 h85),
    fun i h20 h26 h27 h28 => (k.2.2.2.2.2.2 i h20 h26 h27 h28).trans
      (h.2.2.2.2.2.2 i h20 h26 h27 h28)⟩

theorem advance_frame (s : BitRAMState) (b : Bool) : Frame s (advance s b) := by
  simp [Frame, advance]
  constructor <;> intros <;> simp_all

theorem finish_frame (s : BitRAMState) : Frame s (finish s) := by
  simp [Frame, finish]
  intros; simp_all

theorem advance_block (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (b : Bool) (hpc : s.pc = 0)
    (hc : (s.tapes 82).read = some false) (hb : (s.tapes 85).read = some b) :
    PricedSteps (program.next input randomTape) 10 s (advance s b) := by
  apply executeInstructions_sound (instructions := 8)
  simp [executeInstructions, BitRAM.next, program, hpc, hc, hb, advance,
    BitRAMState.setTape, BitRAMState.setRegister, BitTape.write]

theorem finish_block (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 0) (hc : (s.tapes 82).read = some true) :
    PricedSteps (program.next input randomTape) 3 s (finish s) := by
  apply executeInstructions_sound (instructions := 2)
  simp [executeInstructions, BitRAM.next, program, hpc, hc, finish, BitRAMState.setRegister]

theorem loop (input : List Bool) (randomTape : ℕ → Bool)
    (bits preceding : List Bool) (origin : ℤ) (s : BitRAMState) (hpc : s.pc = 0)
    (hc : ∀ k ≤ bits.length, (s.tapes 82).cells ((s.tapes 82).head + k) =
      some (decide (k = bits.length)))
    (hb : ∀ k < bits.length, (s.tapes 85).cells ((s.tapes 85).head + k) = bits[k]?)
    (hout : s.tapes 83 = BitTape.shiftedEnd preceding origin) :
    ∃ t, PricedSteps (program.next input randomTape) (10 * bits.length + 3) s t ∧
      t.pc = 8 ∧
      t.tapes 82 = {s.tapes 82 with head := (s.tapes 82).head + bits.length} ∧
      t.tapes 85 = {s.tapes 85 with head := (s.tapes 85).head + bits.length} ∧
      t.tapes 83 = BitTape.shiftedEnd (preceding ++ bits) origin ∧ Frame s t := by
  induction bits generalizing s preceding with
  | nil =>
    refine ⟨finish s, finish_block input randomTape s hpc (by simpa [BitTape.read] using hc 0 (by simp)),
      rfl, ?_, ?_, ?_, finish_frame s⟩
    · simp [finish]
    · simp [finish]
    · simpa [finish] using hout
  | cons b bits ih =>
    have hclock : (s.tapes 82).read = some false := by simpa [BitTape.read] using hc 0 (by simp)
    have hbit : (s.tapes 85).read = some b := by simpa [BitTape.read] using hb 0 (by simp)
    have he := advance_block input randomTape s b hpc hclock hbit
    have hc' : ∀ k ≤ bits.length, ((advance s b).tapes 82).cells
        (((advance s b).tapes 82).head + k) = some (decide (k = bits.length)) := by
      intro k hk
      have := hc (k + 1) (by simp; omega)
      simpa [advance, Nat.cast_add, add_assoc, add_comm, add_left_comm] using this
    have hb' : ∀ k < bits.length, ((advance s b).tapes 85).cells
        (((advance s b).tapes 85).head + k) = bits[k]? := by
      intro k hk
      have := hb (k + 1) (by simp; omega)
      simpa [advance, Nat.cast_add, add_assoc, add_comm, add_left_comm] using this
    have hout' : (advance s b).tapes 83 = BitTape.shiftedEnd (preceding ++ [b]) origin := by
      simpa [advance, hout] using BitTape.shiftedEnd_append_write preceding origin b
    obtain ⟨t, ht, hp, h82, h85, h83, hf⟩ := ih (preceding ++ [b]) (advance s b) rfl hc' hb' hout'
    refine ⟨t, ?_, hp, ?_, ?_, ?_, (advance_frame s b).trans hf⟩
    · convert he.trans ht using 1; simp; omega
    · simpa [advance, Nat.cast_add, add_assoc, add_comm, add_left_comm] using h82
    · simpa [advance, Nat.cast_add, add_assoc, add_comm, add_left_comm] using h85
    · simpa [List.append_assoc] using h83

def code : Code := .seq (.call program)
  (.seq (.call (Rewind.program 82)) (.call (Rewind.program 83)))

/-- Exactly the payload is copied, including leading zero coefficient bits.
The denominator clock and all persistent banks are restored. -/
theorem executes (input : List Bool) (randomTape : ℕ → Bool)
    (bits : List Bool) (clockOrigin outputOrigin : ℤ) (s : Store)
    (hclock : s.val.tapes 82 = BitTape.shifted (2 ^ bits.length).bits clockOrigin)
    (hbits : ∀ k < bits.length, (s.val.tapes 85).cells ((s.val.tapes 85).head + k) = bits[k]?)
    (hout : s.val.tapes 83 = {BitTape.blank with head := outputOrigin}) :
    ∃ t, Executes input randomTape code (18 * bits.length + 16) s t ∧
      t.val.tapes 82 = s.val.tapes 82 ∧
      t.val.tapes 85 = {s.val.tapes 85 with head := (s.val.tapes 85).head + bits.length} ∧
      t.val.tapes 83 = BitTape.shifted bits outputOrigin ∧
      t.val.inputHead = s.val.inputHead ∧ t.val.address = s.val.address ∧
      t.val.memory = s.val.memory ∧ t.val.randomCursor = s.val.randomCursor ∧
      t.val.output = s.val.output ∧ t.val.registers 23 = s.val.registers 23 ∧
      (∀ i, i ≠ 83 → i ≠ 85 → t.val.tapes i = s.val.tapes i) := by
  have hc : ∀ k ≤ bits.length, (s.val.tapes 82).cells ((s.val.tapes 82).head + k) =
      some (decide (k = bits.length)) := by
    intro k hk
    simp only [hclock, BitTape.shifted, add_sub_cancel_left,
      Int.toNat_natCast, PowerOfTwo.power_bits]
    by_cases heq : k = bits.length
    · subst k; simp
    · have hlt : k < bits.length := by omega
      simp [List.getElem?_append, hlt, heq]
  obtain ⟨a, ea, hap, ha82, ha85, ha83, haf⟩ := loop input randomTape bits [] outputOrigin
    s.val s.property hc hbits (by simpa [BitTape.shiftedEnd, BitTape.shifted, BitTape.blank] using hout)
  have e1 := Executes.call program s a _ ea (by simp [program, hap])
  let a' := Store.ofState a
  have er82 := Rewind.stepsAt 82 clockOrigin input randomTape bits.length a'.val a'.property
    (by simp [a', Store.ofState, ha82, hclock, BitTape.shifted])
    (by simp [a', Store.ofState, ha82, hclock, BitTape.shifted])
    (by
      intro k hk
      refine ⟨false, ?_⟩
      simp [a', Store.ofState, ha82, hclock, BitTape.shifted, PowerOfTwo.power_bits,
        List.getElem?_append, hk])
  let b := Store.ofState (Rewind.finishAt 82 clockOrigin a'.val)
  have e2 : Executes input randomTape (.call (Rewind.program 82)) (4*bits.length+6) a' b :=
    .call _ a' _ _ er82 (by simp [Rewind.program, Rewind.finishAt])
  have hb83 : b.val.tapes 83 = BitTape.shiftedEnd bits outputOrigin := by
    simpa [b, a', Store.ofState, Rewind.finishAt] using ha83
  have er83 := WordTransfer.rewind_shifted 83 outputOrigin input randomTape bits b.val b.property hb83
  let t := Store.ofState (Rewind.finishAt 83 outputOrigin b.val)
  have e3 : Executes input randomTape (.call (Rewind.program 83)) (4*bits.length+6) b t :=
    .call _ b _ _ er83.1 (by simp [Rewind.program, Rewind.finishAt])
  have ht82 : t.val.tapes 82 = s.val.tapes 82 := by
    simp [t, b, a', Store.ofState, Rewind.finishAt, ha82, hclock, BitTape.shifted]
  refine ⟨t, ?_, ht82, ?_, er83.2, haf.2.1, haf.1, haf.2.2.1,
    haf.2.2.2.1, haf.2.2.2.2.1, ?_, ?_⟩
  · convert e1.seq (e2.seq e3) using 1 <;> first | rfl | omega
  · simpa [t, b, a', Store.ofState, Rewind.finishAt] using ha85
  · simpa [t, b, a', Store.ofState, Rewind.finishAt] using
      haf.2.2.2.2.2.2 23 (by decide) (by decide) (by decide) (by decide)
  · intro i hi83 hi85
    by_cases hi82 : i = 82
    · subst i; exact ht82
    · simpa [t, b, a', Store.ofState, Rewind.finishAt, hi83, hi82] using
        haf.2.2.2.2.2.1 i hi82 hi83 hi85

end Maxwell.Cost.NormalizedRecordParser.Payload
