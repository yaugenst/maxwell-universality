import Maxwell.Cost.SignedDifference.Words

namespace Maxwell.Cost.SignedDifference

def padded (bits : List Bool) : List Bool := if bits = [] then [false] else bits

@[simp] theorem padded_value (bits : List Bool) : addressValue (padded bits) = addressValue bits := by
  cases bits <;> simp [padded, addressValue]

theorem padded_pos (bits : List Bool) : 0 < (padded bits).length := by
  cases bits <;> simp [padded]

theorem padded_length (bits : List Bool) : (padded bits).length ≤ bits.length + 1 := by
  cases bits <;> simp [padded]

/-- Padding the zero word is actual Boolean code; the tape origin is
unchanged and no length is supplied as a machine operand. -/
def padProgram (workTape : ℕ) : BitRAM := ⟨[
  .readTape workTape 12 13, .branch 13 4 2,
  .literal 14 false, .writeTape workTape 14, .halt]⟩

def padFinal (workTape : ℕ) (s : BitRAMState) : BitRAMState :=
  if (s.tapes workTape).read.isSome then
    {s with pc := 4, registers := Function.update (Function.update s.registers 12
      ((s.tapes workTape).read.getD false)) 13 true}
  else
    {s with
      pc := 4
      registers := Function.update (Function.update (Function.update s.registers 12 false) 13 false) 14 false
      tapes := Function.update s.tapes workTape ((s.tapes workTape).write (some false))}

def padCost (bits : List Bool) : ℕ := if bits = [] then 5 else 3

theorem pad_cost_le (bits : List Bool) : padCost bits ≤ 5 := by simp [padCost]; split_ifs <;> omega

set_option maxRecDepth 4096 in
theorem pad_steps (workTape : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (s : BitRAMState) (bits : List Bool) (origin : ℤ) (hpc : s.pc = 0)
    (ht : s.tapes workTape = BitTape.shifted bits origin) :
    PricedSteps ((padProgram workTape).next input tape) (padCost bits) s (padFinal workTape s) := by
  cases bits with
  | nil =>
    apply executeInstructions_sound (instructions := 4)
    simp [executeInstructions, padProgram, padCost, padFinal, BitRAM.next, hpc, ht,
      BitRAMState.setTape, BitRAMState.setRegister, BitTape.read, BitTape.shifted]
  | cons b bits =>
    apply executeInstructions_sound (instructions := 2)
    simp [executeInstructions, padProgram, padCost, padFinal, BitRAM.next, hpc, ht,
      BitRAMState.setRegister, BitTape.read, BitTape.shifted]

@[simp] theorem padFinal_pc (workTape : ℕ) (s : BitRAMState) : (padFinal workTape s).pc = 4 := by
  simp [padFinal]; split_ifs <;> rfl

theorem padFinal_tape (workTape : ℕ) (s : BitRAMState) (bits : List Bool) (origin : ℤ)
    (ht : s.tapes workTape = BitTape.shifted bits origin) :
    (padFinal workTape s).tapes workTape = BitTape.shifted (padded bits) origin := by
  cases bits with
  | nil =>
    simp [padFinal, ht, padded, BitTape.read, BitTape.blank]
    have hh := congrArg BitTape.cells (BitTape.shiftedEnd_append_write [] origin false)
    apply BitTape.ext
    · rfl
    · simpa [BitTape.shiftedEnd, BitTape.blank] using hh
  | cons b bits => simp [padFinal, ht, padded]

theorem padFinal_other_tape (workTape i : ℕ) (s : BitRAMState) (hi : i ≠ workTape) :
    (padFinal workTape s).tapes i = s.tapes i := by
  unfold padFinal
  split_ifs <;> simp_all

end Maxwell.Cost.SignedDifference
