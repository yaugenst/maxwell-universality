import Maxwell.Continuum.ContinuumCalibrationEnclosures
import Maxwell.Continuum.FiniteAuxiliaryDyadicBits
import Maxwell.Continuum.SourceDecorationEnumeration

/-! Authoritative physical strength data in chronological vertex order,
shared by the table producer and final record serializer. -/
noncomputable section
namespace Maxwell.Continuum.RealizationParameters
open Maxwell.Composition Maxwell.Composition.SourceDecorationEnumeration
variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

def wellStoredPrecision : ℕ :=
  FiniteAuxiliary.onsitePrecision (length p S hm) (spacing p S hm) (length_pos p S hm)

def wellNumerators (i : ℕ) : ℤ :=
  if hi:i<(vertexList S (precision p S hm)).length then
    (strengthData p S hm (computedEnclosures p S hm).mode (computedEnclosures p S hm).coupling
      (vertexList S (precision p S hm))[i]).numerator
  else 0

theorem wellNumerators_get (i : ℕ) (hi : i<(vertexList S (precision p S hm)).length) :
    wellNumerators p S hm i=
      (strengthData p S hm (computedEnclosures p S hm).mode (computedEnclosures p S hm).coupling
        (vertexList S (precision p S hm))[i]).numerator := by
  simp only [wellNumerators,dite_eq_left hi]

end Maxwell.Continuum.RealizationParameters
