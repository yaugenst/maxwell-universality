import Maxwell.Cost.Blocks
import Maxwell.Cost.Arithmetic.Words
import Maxwell.Cost.ScanOvershoot
import Maxwell.Cost.Multiplication.Value

namespace Maxwell.Cost.HornerMultiply

/-- The multiplier is one fixed list of Boolean and tape instructions.
Tape 1 contains the multiplicand, tape 3 the multiplier read from its end,
and tape 0 the accumulator. Tape 2 is cleared scratch storage. -/
def program : BitRAM := ⟨
  [.readTape 1 12 13, .branch 13 2 71,
   .tapeLeft 3, .readTape 3 12 13, .branch 13 5 71,
   .tapeLeft 0, .literal 14 false, .writeTape 0 14,
   .branch 12 9 2, .literal 2 false] ++
  rippleAdder.code.map (BitRAMInstruction.relocate 10 28) ++
  (RewindOvershoot.program 0).code.map (BitRAMInstruction.relocate 28 37) ++
  (TapeOps.clear 0).code.map (BitRAMInstruction.relocate 37 43) ++
  (Rewind.program 2).code.map (BitRAMInstruction.relocate 43 48) ++
  (TapeOps.copyClear 2 0).code.map (BitRAMInstruction.relocate 48 56) ++
  (Rewind.program 0).code.map (BitRAMInstruction.relocate 56 61) ++
  (RewindOvershoot.program 1).code.map (BitRAMInstruction.relocate 61 70) ++
  [.jump 2, .halt]⟩

theorem program_length : program.code.length = 72 := by decide

theorem contains_add : program.Contains rippleAdder 10 28 := by decide
theorem contains_rewind_left : program.Contains (RewindOvershoot.program 0) 28 37 := by decide
theorem contains_clear : program.Contains (TapeOps.clear 0) 37 43 := by decide
theorem contains_rewind_output : program.Contains (Rewind.program 2) 43 48 := by decide
theorem contains_copy : program.Contains (TapeOps.copyClear 2 0) 48 56 := by decide
theorem contains_rewind_accumulator : program.Contains (Rewind.program 0) 56 61 := by decide
theorem contains_rewind_right : program.Contains (RewindOvershoot.program 1) 61 70 := by decide

/-- Shift one tape word by one binary place using two actual head/write
instructions. The old left neighbor is the blank sentinel. -/
theorem BitTape.prepend_false (bits : List Bool) (origin : ℤ) :
    ({BitTape.shifted bits origin with head := origin - 1}).write (some false) =
      BitTape.shifted (false :: bits) (origin - 1) := by
  apply BitTape.ext
  · rfl
  · funext p
    simp only [BitTape.write, BitTape.shifted]
    by_cases heq : p = origin - 1
    · subst p; simp
    · rw [Function.update_of_ne heq]
      by_cases hp : origin ≤ p
      · have hp' : origin - 1 ≤ p := by omega
        have hi : (p - (origin - 1)).toNat = (p - origin).toNat + 1 := by omega
        simp [hp, hp', hi]
      · have hp' : ¬origin - 1 ≤ p := by omega
        simp [hp, hp']

end Maxwell.Cost.HornerMultiply
