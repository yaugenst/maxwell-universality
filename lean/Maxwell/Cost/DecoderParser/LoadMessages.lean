import Maxwell.Cost.Structured.Correctness
import Maxwell.Cost.Counter
import Maxwell.Cost.MemoryWord.Write
import Mathlib.Data.Nat.Size

/-! A finite uniform loader for raw access messages. The count and address
are stored in binary on tapes 60 and 61; all parser metadata is preserved. -/
namespace Maxwell.Cost.DecoderParser.LoadMessages

open Structured

/-- The incrementer's real carry recurrence never exceeds a sufficient
binary address width, including padded binary representations. -/
theorem carryBits_length_bound (carry : Bool) (word : List Bool) (B : ℕ)
    (hw : word.length ≤ B) (hv : addressValue word + carry.toNat < 2^B) :
    (Increment.carryBits carry word).length ≤ B := by
  induction word generalizing carry B with
  | nil =>
      cases B with
      | zero => cases carry <;> simp_all [Increment.carryBits, addressValue]
      | succ B => cases carry <;> simp [Increment.carryBits]
  | cons a word ih =>
      cases B with
      | zero => simp at hw
      | succ B =>
          have ht : word.length ≤ B := by simpa using hw
          have hval : addressValue word + (a && carry).toNat < 2^B := by
            cases a <;> cases carry <;> simp_all [addressValue, pow_succ] <;> omega
          simpa [Increment.carryBits] using Nat.add_le_add_right (ih (a && carry) B ht hval) 1

theorem increment_length_bound (word : List Bool) (B : ℕ)
    (hw : word.length ≤ B) (hv : addressValue word + 1 < 2^B) :
    (Increment.bits word).length ≤ B := by
  simpa [Increment.bits] using carryBits_length_bound true word B hw hv

structure Frame (s t : BitRAMState) : Prop where
  randomCursor : t.randomCursor = s.randomCursor
  output : t.output = s.output
  tapes : ∀ i, i ≠ 60 → i ≠ 61 → t.tapes i = s.tapes i

theorem Frame.refl (s : BitRAMState) : Frame s s := ⟨rfl, rfl, fun _ _ _ => rfl⟩

theorem Frame.trans {s t u : BitRAMState} (h : Frame s t) (k : Frame t u) : Frame s u :=
  ⟨k.randomCursor.trans h.randomCursor, k.output.trans h.output,
    fun i h60 h61 => (k.tapes i h60 h61).trans (h.tapes i h60 h61)⟩

def flip : BitRAM := ⟨[.bitNot 62 2, .halt]⟩
def flipState (s : BitRAMState) : BitRAMState := s.setRegister 62 (!s.registers 2)

def countdown : Code := .seq (.call (Counter.programOn 60)) (.call flip)

theorem countdown_steps (input : List Bool) (randomTape : ℕ → Bool)
    (counter : List Bool) (s : Store) (hcount : s.val.tapes 60 = BitTape.ofList counter) :
    ∃ t : Store, Executes input randomTape countdown (13 * counter.length + 14) s t ∧
      t.val.tapes 60 = BitTape.ofList (subtractBit true counter) ∧
      (t.val.registers 62 = true ↔ addressValue counter ≠ 0) ∧
      t.val.inputHead = s.val.inputHead ∧ t.val.memory = s.val.memory ∧
      t.val.tapes 61 = s.val.tapes 61 ∧ Frame s.val t.val := by
  obtain ⟨r, hr, hrpc, hri, hrt, hrzero, _, hrf⟩ :=
    Counter.steps_on 60 input randomTape counter s.val s.property hcount
  let middle := Store.ofState r
  have hc := Executes.call (Counter.programOn 60) s r _ hr (by
    have hh : (Counter.programOn 60).code[15]? = some BitRAMInstruction.halt := by decide
    simpa only [hrpc] using hh)
  have hf : Executes input randomTape (.call flip) 2 middle (Store.ofState (flipState middle.val)) := by
    apply Executes.call flip middle (flipState middle.val) 1
    · apply executeInstructions_sound (instructions := 1)
      simp [executeInstructions, BitRAM.next, flip, flipState, middle.property]
    · rfl
  refine ⟨Store.ofState (flipState middle.val), ?_, hrt, ?_, hri, hrf.2.2.1,
    hrf.2.2.2.2.2.1 61 (by omega), ?_⟩
  · convert hc.seq hf using 1; rfl
  · change (!r.registers 2) = true ↔ addressValue counter ≠ 0
    constructor
    · intro hf hz
      have hh := hrzero.mpr hz
      rw [hh] at hf
      contradiction
    · intro hn
      have hh : r.registers 2 = false := Bool.eq_false_iff.mpr (fun hh => hn (hrzero.mp hh))
      rw [hh]
      rfl
  · exact ⟨hrf.2.2.2.1, hrf.2.2.2.2.1, fun i h60 _ => hrf.2.2.2.2.2.1 i h60⟩

def fetch : BitRAM := ⟨[.readSequential 28, .inputRight, .halt]⟩
def fetched (s : BitRAMState) (b : Bool) : BitRAMState :=
  {s with pc := 2, registers := Function.update s.registers 28 b, inputHead := s.inputHead + 1}

def advance : BitRAM := ⟨[.tapeRight 61, .halt]⟩
def advanced (s : BitRAMState) : BitRAMState :=
  s.setTape 61 {s.tapes 61 with head := (s.tapes 61).head + 1}

def writeOne : Code :=
  .seq (.call fetch)
    (.seq (.call (MemoryBit.program 61 (.writeMemory 28)))
      (.seq (.call advance) (.call (Increment.program 61))))

/-- Each bit is read sequentially, written with its full address charge,
and followed by an actual binary address increment. -/
theorem writeOne_steps (input : List Bool) (randomTape : ℕ → Bool)
    (address : List Bool) (b : Bool) (s : Store)
    (ha : s.val.tapes 61 = BitTape.shiftedEnd address 0)
    (hb : inputBit input s.val.inputHead = b) :
    ∃ cost t, cost ≤ 15 * address.length + 21 ∧
      Executes input randomTape writeOne cost s t ∧
      t.val.inputHead = s.val.inputHead + 1 ∧
      t.val.tapes 61 = BitTape.shiftedEnd (Increment.bits address) 0 ∧
      t.val.memory = Function.update s.val.memory (addressValue address) b ∧
      t.val.tapes 60 = s.val.tapes 60 ∧ Frame s.val t.val := by
  let f := Store.ofState (fetched s.val b)
  have ef : Executes input randomTape (.call fetch) 3 s f := by
    apply Executes.call fetch s (fetched s.val b) 2
    · apply executeInstructions_sound (instructions := 2)
      simp [executeInstructions, BitRAM.next, fetch, fetched, s.property, hb, BitRAMState.setRegister]
    · rfl
  obtain ⟨w, ew, hwpc, _, hwm, hwa, hwi, hwr, hwo, hwt, _⟩ :=
    MemoryBit.write_steps 61 input randomTape address 0 f.val f.property ha
  have ewc := Executes.call (MemoryBit.program 61 (.writeMemory 28)) f w _ ew (by
    simp [MemoryBit.program, Address.load, hwpc, BitRAMInstruction.relocate])
  let w' := Store.ofState w
  let a := Store.ofState (advanced w'.val)
  have ea : Executes input randomTape (.call advance) 2 w' a := by
    apply Executes.call advance w' (advanced w'.val) 1
    · apply executeInstructions_sound (instructions := 1)
      simp [executeInstructions, BitRAM.next, advance, advanced, w'.property]
    · rfl
  have hat : a.val.tapes 61 = BitTape.shifted address 0 := by
    simp [a, advanced, Store.ofState, BitRAMState.setTape, w', hwa, BitTape.ofList]
  obtain ⟨icost, t, hicost, eit, htpc, hta, htf⟩ :=
    Increment.simulation 61 input randomTape address 0 a.val a.property hat
  have ei := Executes.call (Increment.program 61) a t _ eit (by simp [Increment.program, htpc])
  refine ⟨3 + ((7 * address.length + 8) + (2 + (icost + 1))), Store.ofState t,
    by omega, ef.seq (ewc.seq (ea.seq ei)), ?_, hta, ?_, ?_, ?_⟩
  · exact htf.2.1.trans hwi
  · exact htf.2.2.1.trans hwm
  · have ht := htf.2.2.2.2.2.1 60 (by omega)
    have hai : a.val.tapes 60 = w.tapes 60 := by
      simp [a, advanced, Store.ofState, BitRAMState.setTape, w']
    exact ht.trans (hai.trans (hwt 60 (by omega)))
  · refine ⟨htf.2.2.2.1.trans hwr, htf.2.2.2.2.1.trans hwo, ?_⟩
    intro i _ hi
    have ht := htf.2.2.2.2.2.1 i hi
    have hai : a.val.tapes i = w.tapes i := by
      simp [a, advanced, Store.ofState, BitRAMState.setTape, hi, w']
    exact ht.trans (hai.trans (hwt i hi))

def loop : Code := .loop 62 (.seq writeOne countdown)
def code : Code := .seq countdown loop

def program : BitRAM := code.compile

/-- The sequential input really contains the designated raw word at the
current head; no host-language read appears in the program. -/
def SequentialWord (input : List Bool) (head : ℤ) (word : List Bool) : Prop :=
  ∀ i : ℕ, ∀ hi : i < word.length, inputBit input (head + i) = word[i]

/-- The loop invariant includes actual remaining count and address bounds.
It allows padding in both binary words. -/
theorem loop_steps (input : List Bool) (randomTape : ℕ → Bool)
    (word address counter : List Bool) (B : ℕ) (s : Store)
    (ha : s.val.tapes 61 = BitTape.shiftedEnd address 0)
    (hwidth : address.length ≤ B) (hmax : addressValue address + word.length < 2^B)
    (hc : s.val.tapes 60 = BitTape.ofList counter)
    (hvalue : 0 < word.length → addressValue counter + 1 = word.length)
    (hflag : s.val.registers 62 = true ↔ 0 < word.length)
    (hread : SequentialWord input s.val.inputHead word) :
    ∃ cost t finalAddress,
      Executes input randomTape loop cost s t ∧
      cost ≤ word.length * (15 * B + 13 * counter.length + 36) + 1 ∧
      t.val.inputHead = s.val.inputHead + word.length ∧
      t.val.tapes 61 = BitTape.shiftedEnd finalAddress 0 ∧
      addressValue finalAddress = addressValue address + word.length ∧
      finalAddress.length ≤ B ∧
      t.val.memory = MemoryWord.writeBits s.val.memory (addressValue address) word ∧ Frame s.val t.val := by
  induction word generalizing address counter s with
  | nil =>
      have hf : s.val.registers 62 = false := Bool.eq_false_iff.mpr (by
        intro hh
        have hz := hflag.mp hh
        simp at hz)
      exact ⟨1, s, address, Executes.done hf, by simp, by simp, ha, by simp,
        hwidth, rfl, Frame.refl _⟩
  | cons b word ih =>
      have hbit : inputBit input s.val.inputHead = b := by
        have hh := hread 0 (by simp)
        change inputBit input (s.val.inputHead + 0) = b at hh
        simpa only [add_zero] using hh
      obtain ⟨wc, w, hwcost, ew, hwi, hwa, hwm, hwcounter, hwframe⟩ :=
        writeOne_steps input randomTape address b s ha hbit
      have hwc : w.val.tapes 60 = BitTape.ofList counter := hwcounter.trans hc
      obtain ⟨c, ec, hct, hcz, hci, hcm, hca, hcframe⟩ := countdown_steps input randomTape counter w hwc
      have hcountervalue : addressValue counter = word.length := by
        have hh := hvalue (by simp)
        simp only [List.length_cons] at hh
        omega
      have hcv : 0 < word.length → addressValue (subtractBit true counter) + 1 = word.length := by
        intro hh
        rw [subtractBit_pred counter (by omega), hcountervalue]
        omega
      have hcf : c.val.registers 62 = true ↔ 0 < word.length := by
        rw [hcz, hcountervalue]
        omega
      have hcad : c.val.tapes 61 = BitTape.shiftedEnd (Increment.bits address) 0 := hca.trans hwa
      have hcw : (Increment.bits address).length ≤ B :=
        increment_length_bound address B hwidth (by simp only [List.length_cons] at hmax; omega)
      have hcmax : addressValue (Increment.bits address) + word.length < 2^B := by
        rw [Increment.bits_value]
        simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmax
      have hcr : SequentialWord input c.val.inputHead word := by
        intro i hi
        have hh := hread (i + 1) (by simpa using hi)
        simpa only [hci, hwi, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm,
          List.getElem_cons_succ] using hh
      obtain ⟨cost, t, finalAddress, et, htcost, hti, hta, htav, htaw, htm, htframe⟩ :=
        ih (Increment.bits address) (subtractBit true counter) c hcad hcw hcmax hct hcv hcf hcr
      refine ⟨1 + (wc + (13 * counter.length + 14)) + cost, t, finalAddress,
        Executes.more (hflag.mpr (by simp)) (ew.seq ec) et, ?_, ?_, hta, ?_, htaw, ?_,
        (hwframe.trans hcframe).trans htframe⟩
      · simp only [subtractBit_length] at htcost
        simp only [List.length_cons]
        have hh : wc ≤ 15 * B + 21 := by omega
        nlinarith
      · simpa only [hci, hwi, List.length_cons, Nat.cast_add, Nat.cast_one,
          add_assoc, add_comm, add_left_comm] using hti
      · simpa only [Increment.bits_value, List.length_cons, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using htav
      · rw [htm, hcm, hwm, Increment.bits_value]
        rfl

/-- Complete uniform execution from the supplied actual binary count. -/
theorem steps (input : List Bool) (randomTape : ℕ → Bool)
    (word address counter : List Bool) (B : ℕ) (s : Store)
    (ha : s.val.tapes 61 = BitTape.shiftedEnd address 0)
    (hwidth : address.length ≤ B) (hmax : addressValue address + word.length < 2^B)
    (hc : s.val.tapes 60 = BitTape.ofList counter)
    (hvalue : addressValue counter = word.length)
    (hread : SequentialWord input s.val.inputHead word) :
    ∃ cost t finalAddress,
      Executes input randomTape code cost s t ∧
      cost ≤ 13 * counter.length + 15 + word.length * (15 * B + 13 * counter.length + 36) ∧
      t.val.inputHead = s.val.inputHead + word.length ∧
      t.val.tapes 61 = BitTape.shiftedEnd finalAddress 0 ∧
      addressValue finalAddress = addressValue address + word.length ∧
      finalAddress.length ≤ B ∧
      t.val.memory = MemoryWord.writeBits s.val.memory (addressValue address) word ∧ Frame s.val t.val := by
  obtain ⟨c, ec, hct, hcz, hci, hcm, hca, hcframe⟩ := countdown_steps input randomTape counter s hc
  have hcv : 0 < word.length → addressValue (subtractBit true counter) + 1 = word.length := by
    intro hh
    rw [subtractBit_pred counter (by omega), hvalue]
    omega
  have hcf : c.val.registers 62 = true ↔ 0 < word.length := by rw [hcz, hvalue]; omega
  obtain ⟨cost, t, finalAddress, et, htcost, hti, hta, htav, htaw, htm, htf⟩ :=
    loop_steps input randomTape word address (subtractBit true counter) B c (hca.trans ha)
      hwidth hmax hct hcv hcf (by simpa only [hci] using hread)
  refine ⟨13 * counter.length + 14 + cost, t, finalAddress, ec.seq et, ?_, ?_, hta, htav, htaw, ?_,
    hcframe.trans htf⟩
  · simp only [subtractBit_length] at htcost
    omega
  · simpa only [hci] using hti
  · simpa only [hcm] using htm

/-- Canonical byte-free serialization supplies the sequential-word premise. -/
theorem sequentialWord_append (preceding word suffix : List Bool) :
    SequentialWord (preceding ++ (word ++ suffix)) preceding.length word := by
  intro i hi
  rw [ParseNat.inputBit_append_offset]
  simp [List.getElem?_append_left hi, List.getElem?_eq_getElem hi]

/-- Literal cost cap: binary count width plus one charged address-width
factor per loaded message bit. -/
def costBound (n : ℕ) : ℕ := 13 * n.bits.length + 15 + n * (28 * n.bits.length + 36)

/-- Load a raw finite word from sequential input into memory addresses
0 through n-1. The input count is its actual canonical binary word. -/
theorem load_word (preceding word suffix : List Bool) (randomTape : ℕ → Bool)
    (s : Store) (hhead : s.val.inputHead = preceding.length)
    (hcount : s.val.tapes 60 = BitTape.ofList word.length.bits)
    (haddress : s.val.tapes 61 = BitTape.blank) :
    ∃ cost t finalAddress,
      Executes (preceding ++ (word ++ suffix)) randomTape code cost s t ∧
      cost ≤ costBound word.length ∧
      t.val.inputHead = s.val.inputHead + word.length ∧
      t.val.tapes 61 = BitTape.shiftedEnd finalAddress 0 ∧
      addressValue finalAddress = word.length ∧ finalAddress.length ≤ word.length.bits.length ∧
      t.val.memory = MemoryWord.writeBits s.val.memory 0 word ∧ Frame s.val t.val := by
  have ha : s.val.tapes 61 = BitTape.shiftedEnd [] 0 := by
    simpa [BitTape.shiftedEnd, BitTape.shifted, BitTape.blank] using haddress
  have hmax : addressValue [] + word.length < 2^word.length.bits.length := by
    simpa only [addressValue, zero_add, Nat.size_eq_bits_len] using Nat.lt_size_self word.length
  obtain ⟨cost, t, finalAddress, he, hc, hi, ha, hv, hw, hm, hf⟩ :=
    steps (preceding ++ (word ++ suffix)) randomTape word [] word.length.bits word.length.bits.length s
      ha (by simp) hmax hcount (addressValue_bits _) (by
        rw [hhead]
        exact sequentialWord_append preceding word suffix)
  refine ⟨cost, t, finalAddress, he, ?_, hi, ha, ?_, hw, hm, hf⟩
  · simpa only [costBound, show 15 * word.length.bits.length + 13 * word.length.bits.length =
      28 * word.length.bits.length by omega] using hc
  · simpa only [addressValue, zero_add] using hv

/-- The compiled loader halts within the explicit cap, preserving every
parser metadata tape, plan tape and arithmetic tape. -/
theorem run_word (preceding word suffix : List Bool) (randomTape : ℕ → Bool)
    (s : Store) (hhead : s.val.inputHead = preceding.length)
    (hcount : s.val.tapes 60 = BitTape.ofList word.length.bits)
    (haddress : s.val.tapes 61 = BitTape.blank) :
    ∃ t : BitRAMState,
      (runPriced (program.next (preceding ++ (word ++ suffix)) randomTape)
        (costBound word.length + 1) s.val).finished = some t ∧
      (runPriced (program.next (preceding ++ (word ++ suffix)) randomTape)
        (costBound word.length + 1) s.val).instructions ≤ costBound word.length ∧
      t.inputHead = s.val.inputHead + word.length ∧
      (∀ i (hi : i < word.length), t.memory i = word[i]) ∧
      (∀ i, word.length ≤ i → t.memory i = s.val.memory i) ∧ Frame s.val t := by
  obtain ⟨cost, t, finalAddress, he, hc, hi, _, _, _, hm, hf⟩ :=
    load_word preceding word suffix randomTape s hhead hcount haddress
  obtain ⟨hfinish, hcost⟩ := he.compiled_run (costBound word.length + 1) (by omega)
  refine ⟨t.place code.size, hfinish, hcost.trans_le hc, hi, ?_, ?_, ⟨hf.randomCursor, hf.output, hf.tapes⟩⟩
  · intro i hil
    change t.val.memory i = _
    rw [hm]
    simpa using MemoryWord.writeBits_inside s.val.memory 0 word i hil
  · intro i hil
    change t.val.memory i = _
    rw [hm]
    exact MemoryWord.writeBits_outside s.val.memory 0 word i (Or.inr (by omega))

/-- The actual raw decoder-message codec has exactly count times fixed width
bits; this theorem loads that concrete codec without redundant framing. -/
theorem load_messages {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n)
    (messages : D.Messages) (preceding suffix : List Bool) (randomTape : ℕ → Bool)
    (s : Store) (hhead : s.val.inputHead = preceding.length)
    (hcount : s.val.tapes 60 = BitTape.ofList (D.sampleCount * D.format.width).bits)
    (haddress : s.val.tapes 61 = BitTape.blank) :
    ∃ t : BitRAMState,
      (runPriced (program.next (preceding ++ (Codec.messages D messages ++ suffix)) randomTape)
        (costBound (D.sampleCount * D.format.width) + 1) s.val).finished = some t ∧
      (runPriced (program.next (preceding ++ (Codec.messages D messages ++ suffix)) randomTape)
        (costBound (D.sampleCount * D.format.width) + 1) s.val).instructions ≤
        costBound (D.sampleCount * D.format.width) ∧
      t.inputHead = s.val.inputHead + (D.sampleCount * D.format.width : ℕ) ∧
      (∀ i (hi : i < (Codec.messages D messages).length), t.memory i = (Codec.messages D messages)[i]) ∧
      (∀ i, D.sampleCount * D.format.width ≤ i → t.memory i = s.val.memory i) ∧ Frame s.val t := by
  have hc : s.val.tapes 60 = BitTape.ofList (Codec.messages D messages).length.bits := by
    simpa only [Codec.messages_length] using hcount
  simpa only [Codec.messages_length] using run_word preceding (Codec.messages D messages) suffix
    randomTape s hhead hc haddress

end Maxwell.Cost.DecoderParser.LoadMessages
