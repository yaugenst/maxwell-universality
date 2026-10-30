import Maxwell.Cost.Structured.Footprint
import Maxwell.Cost.BinaryPrecision

/-! Literal writes preserve unrelated tapes without reducing the rational
literal into its binary digits. -/

namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine
open Maxwell.Cost Maxwell.Cost.Structured

theorem literal_write_protects (target k : ℕ) (xs : List Bool) (hne : target ≠ k) :
    (BinaryPrecision.writeCode target xs).protectsTape k=true := by
  induction xs with
  | nil => rfl
  | cons b rest ih =>
    simp only [BinaryPrecision.writeCode,PowerOfTwo.appendBit,Code.atom,Code.protectsTape,
      BitRAM.protectsTape,BitRAMInstruction.protectsTape,List.all_cons,List.all_nil,
      decide_eq_true hne,Bool.true_and,ih]

#print axioms literal_write_protects

end Maxwell.Continuum.Calibration.ArrayDecodeMachine
