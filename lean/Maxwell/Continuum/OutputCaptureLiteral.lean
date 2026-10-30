import Maxwell.Continuum.OutputCaptureFootprint
import Maxwell.Cost.BinaryPrecision

/-! Capture footprints are independent of the values of literal bit strings. -/
namespace Maxwell.Continuum.OutputCapture
open Maxwell.Cost Maxwell.Cost.Structured

theorem literal_write_avoids (archive target : ℕ) (xs : List Bool) (hne : target≠archive) :
    avoidsCode archive (BinaryPrecision.writeCode target xs)=true := by
  induction xs with
  | nil => rfl
  | cons b rest ih =>
    simp only [BinaryPrecision.writeCode,PowerOfTwo.appendBit,Code.atom,avoidsCode,avoids,
      List.all_cons,List.all_nil,decide_eq_true hne,Bool.true_and,ih]

theorem literal_avoids (archive target n : ℕ) (hne : target≠archive) :
    avoidsCode archive (BinaryPrecision.literalCode target n)=true := by
  simp only [BinaryPrecision.literalCode,avoidsCode,literal_write_avoids archive target n.bits hne,
    Rewind.program,List.all_cons,List.all_nil,avoids,decide_eq_true hne,Bool.true_and]

#print axioms literal_write_avoids
end Maxwell.Continuum.OutputCapture
