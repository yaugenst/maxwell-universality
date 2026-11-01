import Maxwell.Cost.BinaryPrecision
import Maxwell.Cost.Structured.TapeBound

/-! A literal's complete access bound depends only on its destination
tape, including reads performed while rewinding the emitted word. -/
namespace Maxwell.Cost.BinaryPrecision
open Structured

theorem writeCode_bound (target : ℕ) (xs : List Bool) : (writeCode target xs).tapeBound≤target+1 := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons b rest ih =>
    simpa only [writeCode,PowerOfTwo.appendBit,Code.atom,Code.tapeBound,BitRAM.tapeBound,
      List.foldr_cons,List.foldr_nil,BitRAMInstruction.tapeBound,max_self,max_zero,zero_max] using
      max_le le_rfl ih

theorem literalCode_bound (target n : ℕ) : (literalCode target n).tapeBound≤target+1 := by
  simp only [literalCode,Code.tapeBound,max_le_iff]
  exact ⟨writeCode_bound _ _,by
    simp [Rewind.program,BitRAM.tapeBound,BitRAMInstruction.tapeBound]⟩

#print axioms literalCode_bound
end Maxwell.Cost.BinaryPrecision
