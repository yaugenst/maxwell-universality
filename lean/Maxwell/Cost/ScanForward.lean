import Maxwell.Cost.TapeOps

/-! A read-only forward traversal to the first blank cell. This supplies
the actual tape movement between arithmetic results and canonical trimming. -/

namespace Maxwell.Cost.ScanForward

def program (workTape : ℕ) : BitRAM := ⟨[
  .readTape workTape 26 27, .branch 27 2 4,
  .tapeRight workTape, .jump 0, .halt]⟩

def advanceState (workTape : ℕ) (s : BitRAMState) (b : Bool) : BitRAMState :=
  {s with
    pc := 0
    tapes := Function.update s.tapes workTape
      {s.tapes workTape with head := (s.tapes workTape).head + 1}
    registers := Function.update (Function.update s.registers 26 b) 27 true}

def finish (workTape : ℕ) (length : ℕ) (s : BitRAMState) : BitRAMState :=
  {s with
    pc := 4
    tapes := Function.update s.tapes workTape
      {s.tapes workTape with head := (s.tapes workTape).head + length}
    registers := Function.update (Function.update s.registers 26 false) 27 false}

theorem advance_block (workTape : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (b : Bool) (hpc : s.pc = 0)
    (hread : (s.tapes workTape).read = some b) :
    PricedSteps ((program workTape).next input randomTape) 5 s (advanceState workTape s b) := by
  apply executeInstructions_sound (instructions := 4)
  simp [executeInstructions, BitRAM.next, program, advanceState, hpc, hread,
    BitRAMState.setTape, BitRAMState.setRegister]

theorem finish_block (workTape : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (s : BitRAMState) (hpc : s.pc = 0) (hread : (s.tapes workTape).read = none) :
    PricedSteps ((program workTape).next input randomTape) 3 s (finish workTape 0 s) := by
  apply executeInstructions_sound (instructions := 2)
  simp [executeInstructions, BitRAM.next, program, finish, hpc, hread,
    BitRAMState.setRegister]

theorem finish_advance (workTape : ℕ) (length : ℕ) (s : BitRAMState) (b : Bool) :
    finish workTape length (advanceState workTape s b) = finish workTape (length + 1) s := by
  simp [finish, advanceState, add_assoc, add_comm (1 : ℤ)]
  funext i
  by_cases hi : i = 26 <;> by_cases hj : i = 27 <;> simp [hi, hj]

theorem steps (workTape : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (bits : List Bool) (s : BitRAMState) (hpc : s.pc = 0)
    (hword : (s.tapes workTape).Represents bits) :
    PricedSteps ((program workTape).next input randomTape)
      (5 * bits.length + 3) s (finish workTape bits.length s) := by
  induction bits generalizing s with
  | nil =>
    apply finish_block workTape input randomTape s hpc
    simpa [BitTape.read] using hword 0
  | cons b bits ih =>
    have hread : (s.tapes workTape).read = some b := by
      simpa [BitTape.read] using hword 0
    have hs := advance_block workTape input randomTape s b hpc hread
    have ht := ih (advanceState workTape s b) rfl
      (by
        intro k
        have hk := hword (k + 1)
        simpa [advanceState, Nat.cast_add, add_assoc, add_comm, add_left_comm] using hk)
    rw [finish_advance] at ht
    convert hs.trans ht using 1
    simp [Nat.mul_add]
    omega

theorem shifted_steps (workTape : ℕ) (origin : ℤ) (input : List Bool)
    (randomTape : ℕ → Bool) (bits : List Bool) (s : BitRAMState) (hpc : s.pc = 0)
    (hword : s.tapes workTape = BitTape.shifted bits origin) :
    PricedSteps ((program workTape).next input randomTape)
      (5 * bits.length + 3) s (finish workTape bits.length s) ∧
    (finish workTape bits.length s).tapes workTape = BitTape.shiftedEnd bits origin ∧
    TapeOps.Frame workTape workTape s (finish workTape bits.length s) := by
  refine ⟨steps workTape input randomTape bits s hpc ?_, ?_, ?_⟩
  · intro k
    simp [hword, BitTape.shifted]
  · simp [finish, hword, BitTape.shiftedEnd, BitTape.shifted]
  · simp [TapeOps.Frame, finish]
    constructor
    · intro i hi
      simp [hi]
    · intro i h26 h27
      simp [h26, h27]

theorem run (workTape : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (bits : List Bool) (s : BitRAMState) (hpc : s.pc = 0)
    (hword : (s.tapes workTape).Represents bits) :
    (runPriced ((program workTape).next input randomTape)
      (5 * bits.length + 4) s).finished = some (finish workTape bits.length s) ∧
    (runPriced ((program workTape).next input randomTape)
      (5 * bits.length + 4) s).instructions = 5 * bits.length + 3 := by
  exact (steps workTape input randomTape bits s hpc hword).runPriced
    (by simp [BitRAM.next, program, finish])

end Maxwell.Cost.ScanForward
