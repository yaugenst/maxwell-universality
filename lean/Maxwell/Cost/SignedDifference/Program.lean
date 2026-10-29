import Maxwell.Cost.SignedDifference.Value
import Maxwell.Cost.Blocks
import Maxwell.Cost.TrimShifted

namespace Maxwell.Cost.SignedDifference

/-- Fixed signed-magnitude difference code. Padding guarantees that the
rewind calls in the negative branch have discoverable nonempty words. -/
def program : BitRAM := ⟨
  (padProgram 0).code.map (BitRAMInstruction.relocate 0 5) ++
  (padProgram 1).code.map (BitRAMInstruction.relocate 5 10) ++
  Subtraction.program.code.map (BitRAMInstruction.relocate 10 30) ++
  [.bitNot 23 2, .bitNot 23 23, .branch 23 33 82] ++
  (RewindOvershoot.program 0).code.map (BitRAMInstruction.relocate 33 42) ++
  (RewindOvershoot.program 1).code.map (BitRAMInstruction.relocate 42 51) ++
  (Rewind.program 2).code.map (BitRAMInstruction.relocate 51 56) ++
  (TapeOps.clear 2).code.map (BitRAMInstruction.relocate 56 62) ++
  Subtraction.swappedProgram.code.map (BitRAMInstruction.relocate 62 82) ++
  (TapeOps.trim 2).code.map (BitRAMInstruction.relocate 82 91) ++ [.halt]⟩

theorem program_length : program.code.length = 92 := by decide

theorem contains_pad_left : program.Contains (padProgram 0) 0 5 := by decide
theorem contains_pad_right : program.Contains (padProgram 1) 5 10 := by decide
theorem contains_subtract : program.Contains Subtraction.program 10 30 := by decide
theorem contains_rewind_left : program.Contains (RewindOvershoot.program 0) 33 42 := by decide
theorem contains_rewind_right : program.Contains (RewindOvershoot.program 1) 42 51 := by decide
theorem contains_rewind_output : program.Contains (Rewind.program 2) 51 56 := by decide
theorem contains_clear : program.Contains (TapeOps.clear 2) 56 62 := by decide
theorem contains_reverse_subtract : program.Contains Subtraction.swappedProgram 62 82 := by decide
theorem contains_trim : program.Contains (TapeOps.trim 2) 82 91 := by decide

end Maxwell.Cost.SignedDifference
