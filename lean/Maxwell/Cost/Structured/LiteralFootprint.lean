import Maxwell.Cost.BinaryPrecision
import Maxwell.Cost.Structured.TapeBelow
import Maxwell.Cost.Structured.MemoryFootprint
import Maxwell.Cost.Structured.InputPositions

/-! Literal word installation has a footprint independent of the value.
These facts let large static arithmetic constants remain opaque. -/
namespace Maxwell.Cost.BinaryPrecision
open Structured

theorem writeCode_tapesBelow (bound target : ℕ) (xs : List Bool) (ht : target<bound) :
    (writeCode target xs).tapesBelow bound=true := by
  induction xs with
  | nil => rfl
  | cons b rest ih =>
    simp only [writeCode,PowerOfTwo.appendBit,Code.atom,Code.tapesBelow,
      BitRAM.tapesBelow,List.all_cons,List.all_nil,BitRAMInstruction.tapesBelow,
      decide_eq_true ht,Bool.true_and,ih]

theorem literalCode_tapesBelow (bound target n : ℕ) (ht : target<bound) :
    (literalCode target n).tapesBelow bound=true := by
  simp only [literalCode,Code.tapesBelow,writeCode_tapesBelow bound target n.bits ht,
    Rewind.program,BitRAM.tapesBelow,List.all_cons,List.all_nil,BitRAMInstruction.tapesBelow,
    decide_eq_true ht,Bool.true_and]

theorem writeCode_positions (target : ℕ) (xs : List Bool) :
    (writeCode target xs).protectsInputPositions=true := by
  induction xs with
  | nil => rfl
  | cons b rest ih =>
    simp only [writeCode,PowerOfTwo.appendBit,Code.atom,Code.protectsInputPositions,
      BitRAM.protectsInputPositions,List.all_cons,List.all_nil,BitRAMInstruction.protectsInputPositions,
      Bool.true_and,ih]

theorem literalCode_positions (target n : ℕ) :
    (literalCode target n).protectsInputPositions=true := by
  simp only [literalCode,Code.protectsInputPositions,writeCode_positions,
    Rewind.program,BitRAM.protectsInputPositions,List.all_cons,List.all_nil,
    BitRAMInstruction.protectsInputPositions,Bool.true_and]

#print axioms literalCode_tapesBelow
#print axioms literalCode_positions
end Maxwell.Cost.BinaryPrecision
