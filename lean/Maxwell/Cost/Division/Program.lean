import Maxwell.Cost.Division.Value
import Maxwell.Cost.SignedDifference.Words
import Maxwell.Cost.Multiplication.AddCycle

namespace Maxwell.Cost.Division

/-- Fixed binary long division. Tapes 0/1/2 are remainder, divisor and
subtraction scratch; tape 3 is the dividend read backwards, tape 4 the
quotient. All scans and conditional transfers are literal instructions. -/
def program : BitRAM := ⟨
  [.tapeLeft 3, .readTape 3 12 13, .branch 13 3 80,
   .tapeLeft 0, .writeTape 0 12] ++
  Subtraction.program.code.map (BitRAMInstruction.relocate 5 25) ++
  (RewindOvershoot.program 0).code.map (BitRAMInstruction.relocate 25 34) ++
  (RewindOvershoot.program 1).code.map (BitRAMInstruction.relocate 34 43) ++
  (Rewind.program 2).code.map (BitRAMInstruction.relocate 43 48) ++
  [.branch 2 49 56] ++
  (TapeOps.clear 2).code.map (BitRAMInstruction.relocate 49 55) ++
  [.jump 76] ++
  (TapeOps.clear 0).code.map (BitRAMInstruction.relocate 56 62) ++
  (TapeOps.copyClear 2 0).code.map (BitRAMInstruction.relocate 62 70) ++
  (Rewind.program 0).code.map (BitRAMInstruction.relocate 70 75) ++
  [.jump 76, .bitNot 14 2, .tapeLeft 4, .writeTape 4 14, .jump 0, .halt]⟩

theorem program_length : program.code.length = 81 := by decide
theorem contains_subtract : program.Contains Subtraction.program 5 25 := by decide
theorem contains_rewind_remainder : program.Contains (RewindOvershoot.program 0) 25 34 := by decide
theorem contains_rewind_divisor : program.Contains (RewindOvershoot.program 1) 34 43 := by decide
theorem contains_rewind_scratch : program.Contains (Rewind.program 2) 43 48 := by decide
theorem contains_clear_scratch : program.Contains (TapeOps.clear 2) 49 55 := by decide
theorem contains_clear_remainder : program.Contains (TapeOps.clear 0) 56 62 := by decide
theorem contains_copy : program.Contains (TapeOps.copyClear 2 0) 62 70 := by decide
theorem contains_rewind_result : program.Contains (Rewind.program 0) 70 75 := by decide

end Maxwell.Cost.Division
