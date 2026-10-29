import Maxwell.Cost.Arithmetic.Kernel
import Maxwell.Cost.Link
import Maxwell.Cost.Scan

namespace Maxwell.Cost

def subtractBit (borrow : Bool) : List Bool → List Bool
  | [] => []
  | a :: xs => xor a borrow :: subtractBit ((!a) && borrow) xs

def finalBorrow (borrow : Bool) : List Bool → Bool
  | [] => borrow
  | a :: xs => finalBorrow ((!a) && borrow) xs

@[simp] theorem subtractBit_length (borrow : Bool) (xs : List Bool) :
    (subtractBit borrow xs).length = xs.length := by
  induction xs generalizing borrow with
  | nil => rfl
  | cons a xs ih => simp [subtractBit, ih]

theorem subtract_bit_value (a borrow : Bool) :
    (xor a borrow).toNat + borrow.toNat = a.toNat + 2 * ((!a) && borrow).toNat := by
  cases a <;> cases borrow <;> decide

theorem subtractBit_value (borrow : Bool) (xs : List Bool) :
    addressValue (subtractBit borrow xs) + borrow.toNat =
      addressValue xs + 2 ^ xs.length * (finalBorrow borrow xs).toNat := by
  induction xs generalizing borrow with
  | nil => simp [subtractBit, finalBorrow, addressValue]
  | cons a xs ih =>
    have hv := subtract_bit_value a borrow
    have ht := ih ((!a) && borrow)
    simp only [subtractBit, finalBorrow, addressValue, List.length_cons, pow_succ]
    nlinarith

theorem finalBorrow_true_iff (borrow : Bool) (xs : List Bool) :
    finalBorrow borrow xs = true ↔ borrow = true ∧ addressValue xs = 0 := by
  induction xs generalizing borrow with
  | nil => simp [finalBorrow, addressValue]
  | cons a xs ih =>
    rw [finalBorrow, ih]
    cases a <;> cases borrow <;> simp [addressValue]

theorem subtractBit_pred (xs : List Bool) (h : 0 < addressValue xs) :
    addressValue (subtractBit true xs) = addressValue xs - 1 := by
  have hz : finalBorrow true xs = false := by
    apply Bool.eq_false_iff.mpr
    intro hc
    have heq := (finalBorrow_true_iff true xs).mp hc
    omega
  have hv := subtractBit_value true xs
  simp only [hz, Bool.toNat_false, Bool.toNat_true, mul_zero, add_zero] at hv
  omega

theorem addressValue_bits (n : ℕ) : addressValue n.bits = n := by
  have heq : ∀ xs : List Bool, addressValue xs = Codec.bitsValue xs := by
    intro xs
    induction xs with
    | nil => rfl
    | cons b bs ih => simp [addressValue, Codec.bitsValue, ih]
  rw [heq, Codec.bitsValue_bits]

/-- One fixed binary decrement program. Tape 0 holds little-endian bits;
register 2 reports underflow (equivalently the original number was zero).
The routine deliberately preserves word length, so repeated counters need
no canonicalization or uncharged host-length computation. -/
def binaryCounter : BitRAM := ⟨[
  .literal 2 true,
  .readTape 0 0 1,
  .branch 1 3 9,
  .bitXor 3 0 2,
  .bitNot 4 0,
  .bitAnd 2 4 2,
  .writeTape 0 3,
  .tapeRight 0,
  .jump 1,
  .halt]⟩

def CounterFrame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, i ≠ 0 → t.tapes i = s.tapes i) ∧
  (∀ i, 4 < i → t.registers i = s.registers i)

theorem CounterFrame.refl (s : BitRAMState) : CounterFrame s s := by simp [CounterFrame]

theorem CounterFrame.trans {s t u : BitRAMState} (h : CounterFrame s t)
    (k : CounterFrame t u) : CounterFrame s u := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  rcases k with ⟨ka, ki, km, kr, ko, kt, kg⟩
  exact ⟨ka.trans ha, ki.trans hi, km.trans hm, kr.trans hr, ko.trans ho,
    fun i hn => (kt i hn).trans (ht i hn), fun i hn => (kg i hn).trans (hg i hn)⟩

theorem binaryCounter_next_frame (input : List Bool) (tape : ℕ → Bool)
    {s : BitRAMState} {step : PricedStep BitRAMState}
    (h : binaryCounter.next input tape s = some step) : CounterFrame s step.state := by
  have hlt : s.pc < 10 := by
    by_contra! hge
    have hnone : binaryCounter.code[s.pc]? = none :=
      List.getElem?_eq_none (by simpa [binaryCounter] using hge)
    simp [BitRAM.next, hnone] at h
  generalize hp : s.pc = pc at hlt
  interval_cases pc <;> simp [BitRAM.next, binaryCounter, hp] at h
  all_goals subst step
  all_goals simp [CounterFrame, BitRAMState.setRegister, BitRAMState.setTape,
    Function.update_apply]
  all_goals
    intros
    try split_ifs
    all_goals first | rfl | omega

theorem binaryCounter_steps_frame (input : List Bool) (tape : ℕ → Bool)
    {cost : ℕ} {s t : BitRAMState} (h : PricedSteps (binaryCounter.next input tape) cost s t) :
    CounterFrame s t := by
  induction h with
  | refl s => exact CounterFrame.refl s
  | step h rest ih => exact (binaryCounter_next_frame input tape h).trans ih

def counterRound (s : BitRAMState) : BitRAMState :=
  let s := {readTapeState s 0 0 1 with pc := 3}
  let s := s.setRegister 3 (xor (s.registers 0) (s.registers 2))
  let s := s.setRegister 4 (!s.registers 0)
  let s := s.setRegister 2 (s.registers 4 && s.registers 2)
  let s := s.setTape 0 ((s.tapes 0).write (some (s.registers 3)))
  let s := s.setTape 0 {s.tapes 0 with head := (s.tapes 0).head + 1}
  {s with pc := 1}

def counterStopped (s : BitRAMState) : BitRAMState :=
  {readTapeState s 0 0 1 with pc := 9}

set_option maxRecDepth 4096 in
theorem counterRound_execute (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 1) (a : Bool)
    (ha : (s.tapes 0).read = some a) :
    executeInstructions (binaryCounter.next input tape) 8 s =
      some (counterRound s, 9) := by
  simp [executeInstructions, binaryCounter, BitRAM.next, hpc,
    counterRound, readTapeState, BitTape.write, ha]

theorem counterStop_execute (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 1) (ha : (s.tapes 0).read = none) :
    executeInstructions (binaryCounter.next input tape) 2 s =
      some (counterStopped s, 3) := by
  simp [executeInstructions, binaryCounter, BitRAM.next, hpc, ha,
    counterStopped, readTapeState]

@[simp] theorem counterStopped_halt (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) : binaryCounter.next input tape (counterStopped s) = none := rfl

@[simp] theorem counterRound_borrow (s : BitRAMState) :
    (counterRound s).registers 2 =
      ((!(s.tapes 0).read.getD false) && s.registers 2) := by
  simp [counterRound, readTapeState]

@[simp] theorem counterStopped_borrow (s : BitRAMState) :
    (counterStopped s).registers 2 = s.registers 2 := by
  simp [counterStopped, readTapeState]

@[simp] theorem counterStopped_tape (s : BitRAMState) :
    (counterStopped s).tapes = s.tapes := rfl

theorem counterRound_writes (s : BitRAMState) :
    TapeWrites (s.tapes 0) ((counterRound s).tapes 0)
      [xor ((s.tapes 0).read.getD false) (s.registers 2)] := by
  constructor <;> simp [counterRound, readTapeState, BitTape.write, writeCells]

theorem counterRound_tail {s : BitRAMState} {a : Bool} {xs : List Bool}
    (h : TapeRepresents (s.tapes 0) (a :: xs)) :
    TapeRepresents ((counterRound s).tapes 0) xs := by
  intro k
  have hh := h (k + 1)
  simp only [List.getElem?_cons_succ] at hh
  change Function.update (s.tapes 0).cells (s.tapes 0).head
    (some (xor ((s.tapes 0).read.getD false) (s.registers 2)))
    ((s.tapes 0).head + 1 + (k : ℤ)) = xs[k]?
  rw [Function.update_of_ne (by omega : (s.tapes 0).head + 1 + (k : ℤ) ≠ (s.tapes 0).head)]
  simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using hh

/-- The loop proof follows the real transitions for every possible width. -/
theorem counter_loop_simulation (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (xs : List Bool) (hpc : s.pc = 1)
    (hx : TapeRepresents (s.tapes 0) xs) :
    ∃ final, PricedSteps (binaryCounter.next input tape) (9 * xs.length + 3) s final ∧
      final.pc = 9 ∧
      binaryCounter.next input tape final = none ∧
      TapeWrites (s.tapes 0) (final.tapes 0) (subtractBit (s.registers 2) xs) ∧
      final.registers 2 = finalBorrow (s.registers 2) xs := by
  induction xs generalizing s with
  | nil =>
    refine ⟨counterStopped s, ?_, rfl, by simp, ?_, ?_⟩
    · simpa using executeInstructions_sound _ (counterStop_execute input tape s hpc hx.read)
    · simpa [subtractBit] using TapeWrites.refl (s.tapes 0)
    · simp [finalBorrow]
  | cons a xs ih =>
    have hr := executeInstructions_sound _ (counterRound_execute input tape s hpc a hx.read)
    obtain ⟨final, hsteps, hfinalpc, hhalt, hwrites, hborrow⟩ :=
      ih (counterRound s) rfl (counterRound_tail hx)
    refine ⟨final, ?_, hfinalpc, hhalt, ?_, ?_⟩
    · convert hr.trans hsteps using 1
      simp
      omega
    · have hw := (counterRound_writes s).trans hwrites
      simpa [subtractBit, hx.read] using hw
    · simpa [finalBorrow, hx.read] using hborrow

/-- Exact charged running time, including initialization and the final
zero test. The same code works for leading-zero and canonical words. -/
theorem binaryCounter_simulation (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (xs : List Bool) (hpc : s.pc = 0)
    (hx : TapeRepresents (s.tapes 0) xs) :
    ∃ final, PricedSteps (binaryCounter.next input tape) (9 * xs.length + 4) s final ∧
      final.pc = 9 ∧
      binaryCounter.next input tape final = none ∧
      TapeWrites (s.tapes 0) (final.tapes 0) (subtractBit true xs) ∧
      (final.registers 2 = true ↔ addressValue xs = 0) ∧
      addressValue (subtractBit true xs) + 1 =
        addressValue xs + 2 ^ xs.length * (final.registers 2).toNat := by
  let initialized := s.setRegister 2 true
  have hi : binaryCounter.next input tape s = some ⟨initialized, 0⟩ := by
    simp [binaryCounter, BitRAM.next, hpc, initialized]
  obtain ⟨final, hsteps, hfinalpc, hhalt, hwrites, hborrow⟩ :=
    counter_loop_simulation input tape initialized xs (by simp [initialized, hpc])
      (by simpa [initialized] using hx)
  refine ⟨final, ?_, hfinalpc, hhalt, ?_, ?_, ?_⟩
  · convert PricedSteps.step hi hsteps using 1
    omega
  · simpa [initialized] using hwrites
  · simpa [initialized, hborrow] using finalBorrow_true_iff true xs
  · simpa [initialized, hborrow] using subtractBit_value true xs

theorem writeCells_preserves_right (cells : ℤ → Option Bool) (start point : ℤ)
    (xs : List Bool) (h : start + xs.length ≤ point) :
    writeCells cells start xs point = cells point := by
  induction xs generalizing cells start with
  | nil => rfl
  | cons x xs ih =>
    rw [writeCells, ih _ _ (by simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h; omega)]
    exact Function.update_of_ne (by simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at h; omega) _ _

/-- Replacing a complete word of the same width leaves no hidden cells. -/
theorem TapeWrites.ofList {xs ys : List Bool} {after : BitTape}
    (h : TapeWrites (BitTape.ofList xs) after ys) (hlen : ys.length = xs.length) :
    after = BitTape.atEnd ys := by
  apply BitTape.ext
  · simpa [BitTape.ofList, BitTape.atEnd] using h.head
  · funext p
    rw [h.cells]
    change writeCells (BitTape.ofList xs).cells 0 ys p = (BitTape.atEnd ys).cells p
    by_cases hp : p < 0
    · rw [writeCells_preserves_left _ _ _ _ hp]
      simp [BitTape.ofList, BitTape.atEnd, show ¬ 0 ≤ p by omega]
    · have hnonneg : 0 ≤ p := by omega
      have hnat : (p.toNat : ℤ) = p := by omega
      by_cases hk : p.toNat < ys.length
      · have hh := writeCells_read (BitTape.ofList xs).cells 0 ys p.toNat hk
        simpa [BitTape.ofList, BitTape.atEnd, hnat, hnonneg] using hh
      · rw [writeCells_preserves_right _ _ _ _ (by omega)]
        simp [BitTape.ofList, BitTape.atEnd, hnonneg,
          List.getElem?_eq_none (by omega : xs.length ≤ p.toNat),
          List.getElem?_eq_none (by omega : ys.length ≤ p.toNat)]

namespace Counter

def FrameAt (workTape : ℕ) (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, i ≠ workTape → t.tapes i = s.tapes i) ∧
  (∀ i, 4 < i → i ≠ 24 → i ≠ 25 → t.registers i = s.registers i)

abbrev Frame := FrameAt 0

def rewindPreamble : List BitRAMInstruction :=
  binaryCounter.code.map (BitRAMInstruction.relocate 0 10)

def counterSuffix : List BitRAMInstruction :=
  (Rewind.program 0).code.map (BitRAMInstruction.relocate 10 15) ++ [.halt]

/-- The same-width decrement is followed by a counted rewind. Tape 0 can
therefore be used for another iteration immediately. Register 2 is true
exactly on the terminating underflow case. -/
def program : BitRAM := BitRAM.link [] binaryCounter 10 counterSuffix

theorem rewindPreamble_length : rewindPreamble.length = 10 := by
  simp [rewindPreamble, binaryCounter]

theorem program_as_rewind :
    program = BitRAM.link rewindPreamble (Rewind.program 0) 15 [.halt] := by
  simp only [program, BitRAM.link, rewindPreamble_length]
  simp [rewindPreamble, counterSuffix]

theorem steps (input : List Bool) (tape : ℕ → Bool) (xs : List Bool)
    (initial : BitRAMState) (hpc : initial.pc = 0)
    (hword : initial.tapes 0 = BitTape.ofList xs) :
    ∃ final : BitRAMState,
      PricedSteps (program.next input tape) (13 * xs.length + 11) initial final ∧
      final.pc = 15 ∧ final.inputHead = initial.inputHead ∧
      final.tapes 0 = BitTape.ofList (subtractBit true xs) ∧
      (final.registers 2 = true ↔ addressValue xs = 0) ∧
      addressValue (subtractBit true xs) + 1 =
        addressValue xs + 2 ^ xs.length * (final.registers 2).toNat ∧
      Frame initial final := by
  obtain ⟨s, hs, hspc, _, hwrites, hzero, hvalue⟩ :=
    binaryCounter_simulation input tape initial xs hpc
      (by rw [hword]; exact BitTape.ofList_represents xs)
  have hframe := binaryCounter_steps_frame input tape hs
  have hstape : s.tapes 0 = BitTape.atEnd (subtractBit true xs) := by
    rw [hword] at hwrites
    exact hwrites.ofList (subtractBit_length true xs)
  have hsLinked := hs.link [] 10 counterSuffix
  simp only [List.length_nil, BitRAMState.relocate, Nat.zero_add] at hsLinked
  change PricedSteps (program.next input tape) _ initial s at hsLinked
  have hsReturn : PricedSteps (program.next input tape) 1 s {s with pc := 10} := by
    simpa only [List.length_nil, BitRAMState.relocate, Nat.zero_add, program] using
      (PricedSteps.step (BitRAM.link_return [] binaryCounter 10 counterSuffix input tape s
        (by simp [binaryCounter, hspc])) (PricedSteps.refl _))
  let rewindStart := {s with pc := 0}
  have hr := Rewind.atEnd_steps 0 input tape (subtractBit true xs) rewindStart rfl hstape
  have hrLinked := hr.link rewindPreamble 15 [.halt]
  rw [← program_as_rewind, rewindPreamble_length] at hrLinked
  have hstart : rewindStart.relocate 10 = {s with pc := 10} := by
    simp [rewindStart, BitRAMState.relocate]
  rw [hstart] at hrLinked
  let result := Rewind.finish 0 rewindStart
  have hrReturn : PricedSteps (program.next input tape) 1
      (result.relocate 10) {result with pc := 15} := by
    rw [program_as_rewind]
    simpa only [rewindPreamble_length] using
      (PricedSteps.step (BitRAM.link_return rewindPreamble (Rewind.program 0) 15 [.halt]
        input tape result (by simp [result, Rewind.finish, Rewind.program])) (PricedSteps.refl _))
  have hall : PricedSteps (program.next input tape) (13 * xs.length + 11)
      initial {result with pc := 15} := by
    convert ((hsLinked.trans hsReturn).trans hrLinked).trans hrReturn using 1
    simp
    omega
  refine ⟨{result with pc := 15}, hall, rfl, hframe.2.1, ?_, ?_, ?_, ?_⟩
  · exact Rewind.finish_tape 0 _ rewindStart hstape
  · simpa [result, Rewind.finish] using hzero
  · simpa [result, Rewind.finish] using hvalue
  · rcases hframe with ⟨ha, hi, hm, hr, ho, ht, hg⟩
    refine ⟨ha, hi, hm, hr, ho, ?_, ?_⟩
    · intro i hne
      simpa [result, Rewind.finish, rewindStart, Function.update_of_ne hne] using ht i hne
    · intro i hgt h24 h25
      simpa [result, Rewind.finish, rewindStart, Function.update_of_ne h24,
        Function.update_of_ne h25] using hg i hgt

theorem run_word (input : List Bool) (tape : ℕ → Bool) (xs : List Bool)
    (initial : BitRAMState) (hpc : initial.pc = 0)
    (hword : initial.tapes 0 = BitTape.ofList xs) :
    ∃ final : BitRAMState,
      (runPriced (program.next input tape) (13 * xs.length + 12) initial).finished = some final ∧
      (runPriced (program.next input tape) (13 * xs.length + 12) initial).instructions =
        13 * xs.length + 11 ∧
      final.tapes 0 = BitTape.ofList (subtractBit true xs) ∧
      (final.registers 2 = true ↔ addressValue xs = 0) ∧ Frame initial final := by
  obtain ⟨final, hs, hpc, _, ht, hz, _, hf⟩ := steps input tape xs initial hpc hword
  have hhalt : program.next input tape final = none := by
    have hc : program.code[15]? = some .halt := by decide
    simp [BitRAM.next, hpc, hc]
  obtain ⟨hfinish, hcost⟩ := hs.runPriced hhalt
  exact ⟨final, hfinish, hcost, ht, hz, hf⟩

def programOn (workTape : ℕ) : BitRAM := program.renameTapes (Equiv.swap 0 workTape)

/-- A literal tape permutation makes the countdown routine available on
the list parser's private counter tape, with the same exact cost. -/
theorem steps_on (workTape : ℕ) (input : List Bool) (tape : ℕ → Bool) (xs : List Bool)
    (initial : BitRAMState) (hpc : initial.pc = 0)
    (hword : initial.tapes workTape = BitTape.ofList xs) :
    ∃ final : BitRAMState,
      PricedSteps ((programOn workTape).next input tape) (13 * xs.length + 11) initial final ∧
      final.pc = 15 ∧ final.inputHead = initial.inputHead ∧
      final.tapes workTape = BitTape.ofList (subtractBit true xs) ∧
      (final.registers 2 = true ↔ addressValue xs = 0) ∧
      addressValue (subtractBit true xs) + 1 =
        addressValue xs + 2 ^ xs.length * (final.registers 2).toNat ∧
      FrameAt workTape initial final := by
  let p : Equiv.Perm ℕ := Equiv.swap 0 workTape
  obtain ⟨s, hs, hspc, hshead, hsword, hzero, hvalue, hframe⟩ :=
    steps input tape xs (initial.renameTapes p.symm) hpc
      (by simpa [BitRAMState.renameTapes, p] using hword)
  have hinverse : (initial.renameTapes p.symm).renameTapes p = initial := by
    cases initial
    simp [BitRAMState.renameTapes, Function.comp_def]
  have hrenamed := hs.renameTapes p
  rw [hinverse] at hrenamed
  refine ⟨s.renameTapes p, hrenamed, hspc, hshead, ?_, hzero, hvalue, ?_⟩
  · simpa [BitRAMState.renameTapes, p] using hsword
  · rcases hframe with ⟨ha, hi, hm, hr, ho, ht, hg⟩
    refine ⟨ha, hi, hm, hr, ho, ?_, hg⟩
    intro i hne
    have hp : p.symm i ≠ 0 := by
      intro heq
      have hh := congrArg p heq
      simp [p] at hh
      exact hne hh
    simpa [BitRAMState.renameTapes, Function.comp_def] using ht (p.symm i) hp

end Counter

end Maxwell.Cost
