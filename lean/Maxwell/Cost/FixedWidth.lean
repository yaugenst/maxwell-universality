import Maxwell.Cost.Arithmetic.Words

namespace Maxwell.Cost.FixedWidth

/-- Exactly the requested width, with high zeros after the source ends. -/
def bits : ℕ → List Bool → List Bool
  | 0, _ => []
  | n + 1, xs => xs.head?.getD false :: bits n xs.tail

@[simp] theorem bits_length (width : ℕ) (xs : List Bool) : (bits width xs).length = width := by
  induction width generalizing xs with
  | zero => rfl
  | succ width ih => simp [bits, ih]

theorem bits_empty (width : ℕ) : bits width [] = List.replicate width false := by
  induction width with
  | zero => rfl
  | succ width ih => simp [bits, ih, List.replicate_succ]

theorem bits_eq_pad (width : ℕ) (xs : List Bool) (h : xs.length ≤ width) :
    bits width xs = xs ++ List.replicate (width - xs.length) false := by
  induction width generalizing xs with
  | zero => have hx : xs = [] := by simpa using h
            subst xs
            rfl
  | succ width ih =>
    cases xs with
    | nil => simpa using bits_empty (width + 1)
    | cons b xs => simpa [bits] using congrArg (List.cons b) (ih xs (by simpa using h))

theorem bits_value (width : ℕ) (xs : List Bool) (h : xs.length ≤ width) :
    addressValue (bits width xs) = addressValue xs := by
  rw [bits_eq_pad width xs h, TapeOps.addressValue_append_zeros]

/-- Tape identifiers are static program parameters. Width is read from an
actual clock word, one symbol per output bit, without host arithmetic. -/
def program (source clock target : ℕ) : BitRAM := ⟨[
  .readTape clock 26 27, .branch 27 2 8, .readTape source 28 29,
  .writeTape target 28, .tapeRight source, .tapeRight clock, .tapeRight target,
  .jump 0, .halt]⟩

def Frame (source clock target : ℕ) (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, i ≠ source → i ≠ clock → i ≠ target → t.tapes i = s.tapes i) ∧
  (∀ i, i ≠ 26 → i ≠ 27 → i ≠ 28 → i ≠ 29 → t.registers i = s.registers i)

theorem Frame.trans {source clock target : ℕ} {s t u : BitRAMState}
    (h : Frame source clock target s t) (k : Frame source clock target t u) :
    Frame source clock target s u := by
  rcases h with ⟨ha, hi, hm, hr, ho, ht, hg⟩
  rcases k with ⟨ka, ki, km, kr, ko, kt, kg⟩
  exact ⟨ka.trans ha, ki.trans hi, km.trans hm, kr.trans hr, ko.trans ho,
    fun i hs hc ht' => (kt i hs hc ht').trans (ht i hs hc ht'),
    fun i h26 h27 h28 h29 => (kg i h26 h27 h28 h29).trans (hg i h26 h27 h28 h29)⟩

def advanced (source clock target : ℕ) (s : BitRAMState) (clockBit : Bool)
    (sourceBit : Option Bool) : BitRAMState :=
  {s with
    pc := 0
    registers := Function.update (Function.update (Function.update (Function.update
      s.registers 26 clockBit) 27 true) 28 (sourceBit.getD false)) 29 sourceBit.isSome
    tapes := Function.update (Function.update (Function.update s.tapes source
      {s.tapes source with head := (s.tapes source).head + 1}) clock
      {s.tapes clock with head := (s.tapes clock).head + 1}) target
      {(s.tapes target).write (some (sourceBit.getD false)) with head := (s.tapes target).head + 1}}

def stopped (s : BitRAMState) : BitRAMState :=
  {s with pc := 8, registers := Function.update (Function.update s.registers 26 false) 27 false}

theorem advance_steps (source clock target : ℕ)
    (hsc : source ≠ clock) (hst : source ≠ target) (hct : clock ≠ target)
    (input : List Bool) (randomTape : ℕ → Bool) (s : BitRAMState)
    (clockBit : Bool) (sourceBit : Option Bool) (hpc : s.pc = 0)
    (hc : (s.tapes clock).read = some clockBit) (hs : (s.tapes source).read = sourceBit) :
    PricedSteps ((program source clock target).next input randomTape) 10 s
      (advanced source clock target s clockBit sourceBit) := by
  apply executeInstructions_sound (instructions := 8)
  simp [executeInstructions, program, BitRAM.next, hpc, hc, hs, advanced,
    BitRAMState.setTape, BitRAMState.setRegister, hsc, hst, hct,
    Ne.symm hsc, Ne.symm hst, Ne.symm hct, Function.update_comm, BitTape.write]

theorem stop_steps (source clock target : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 0) (hc : (s.tapes clock).read = none) :
    PricedSteps ((program source clock target).next input randomTape) 3 s (stopped s) := by
  apply executeInstructions_sound (instructions := 2)
  simp [executeInstructions, program, BitRAM.next, hpc, hc, stopped, BitRAMState.setRegister]

theorem advanced_frame (source clock target : ℕ) (s : BitRAMState) (b : Bool) (a : Option Bool) :
    Frame source clock target s (advanced source clock target s b a) := by
  simp [Frame, advanced]
  constructor <;> intros <;> simp_all

theorem stopped_frame (source clock target : ℕ) (s : BitRAMState) :
    Frame source clock target s (stopped s) := by
  simp [Frame, stopped]
  intros
  simp_all

theorem represents_tail {tape : BitTape} {xs : List Bool} (h : TapeRepresents tape xs) :
    TapeRepresents {tape with head := tape.head + 1} xs.tail := by
  intro k
  have hh := h (k + 1)
  simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm, List.getElem?_tail] using hh

/-- Complete operational loop, retaining even the source's cells beyond
its logical end and charging every blank/default-zero input read. -/
theorem loop (source clock target : ℕ)
    (hsc : source ≠ clock) (hst : source ≠ target) (hct : clock ≠ target)
    (input : List Bool) (randomTape : ℕ → Bool) (clockWord xs : List Bool)
    (s : BitRAMState) (hpc : s.pc = 0)
    (hc : TapeRepresents (s.tapes clock) clockWord)
    (hs : TapeRepresents (s.tapes source) xs) :
    ∃ t, PricedSteps ((program source clock target).next input randomTape)
        (10 * clockWord.length + 3) s t ∧ t.pc = 8 ∧
      t.tapes source = {s.tapes source with head := (s.tapes source).head + clockWord.length} ∧
      t.tapes clock = {s.tapes clock with head := (s.tapes clock).head + clockWord.length} ∧
      TapeWrites (s.tapes target) (t.tapes target) (bits clockWord.length xs) ∧
      Frame source clock target s t := by
  induction clockWord generalizing xs s with
  | nil =>
    refine ⟨stopped s, ?_, rfl, ?_, ?_, TapeWrites.refl _, stopped_frame source clock target s⟩
    · simpa using stop_steps source clock target input randomTape s hpc hc.read
    · simp [stopped]
    · simp [stopped]
  | cons b clockWord ih =>
    have hstep := advance_steps source clock target hsc hst hct input randomTape s b
      xs.head? hpc hc.read hs.read
    let next := advanced source clock target s b xs.head?
    have hnc : TapeRepresents (next.tapes clock) clockWord := by
      simpa [next, advanced, hct] using hc.moveRight
    have hns : TapeRepresents (next.tapes source) xs.tail := by
      simpa [next, advanced, hsc, hst] using represents_tail hs
    obtain ⟨t, ht, hp, hsource, hclock, hw, hf⟩ := ih xs.tail next rfl hnc hns
    have hw0 : TapeWrites (s.tapes target) (next.tapes target) [xs.head?.getD false] := by
      constructor <;> simp [next, advanced, writeCells, BitTape.write]
    refine ⟨t, ?_, hp, ?_, ?_, ?_, (advanced_frame source clock target s b xs.head?).trans hf⟩
    · convert hstep.trans ht using 1
      simp
      omega
    · simpa [next, advanced, hsc, hst, Nat.cast_add, add_assoc, add_comm] using hsource
    · simpa [next, advanced, hct, Nat.cast_add, add_assoc, add_comm] using hclock
    · simpa [bits] using hw0.trans hw

/-- One uniform finite program emits a globally represented fixed-width
word. Its output value equals the input whenever the requested width fits. -/
theorem simulation (source clock target : ℕ)
    (hsc : source ≠ clock) (hst : source ≠ target) (hct : clock ≠ target)
    (input : List Bool) (randomTape : ℕ → Bool) (clockWord xs : List Bool)
    (so co targetOrigin : ℤ) (s : BitRAMState) (hpc : s.pc = 0)
    (hc : s.tapes clock = BitTape.shifted clockWord co)
    (hs : s.tapes source = BitTape.shifted xs so)
    (ht : s.tapes target = {BitTape.blank with head := targetOrigin}) :
    ∃ t, PricedSteps ((program source clock target).next input randomTape)
        (10 * clockWord.length + 3) s t ∧ t.pc = 8 ∧
      t.tapes source = {BitTape.shifted xs so with head := so + clockWord.length} ∧
      t.tapes clock = BitTape.shiftedEnd clockWord co ∧
      t.tapes target = BitTape.shiftedEnd (bits clockWord.length xs) targetOrigin ∧
      Frame source clock target s t := by
  obtain ⟨t, he, hp, hsource, hclock, hw, hf⟩ :=
    loop source clock target hsc hst hct input randomTape clockWord xs s hpc
      (hc ▸ BitTape.shifted_represents clockWord co) (hs ▸ BitTape.shifted_represents xs so)
  exact ⟨t, he, hp, by simpa [hs, BitTape.shifted] using hsource,
    by simpa [hc, BitTape.shiftedEnd, BitTape.shifted] using hclock, hw.blank ht, hf⟩

end Maxwell.Cost.FixedWidth
