import Maxwell.Continuum.CalibrationCoefficientEntries
import Maxwell.Continuum.CalibrationRawCoordinates

/-! Literal quotient/remainder decoding of the existing finite alias
array index. The formulas are the inputs to the fixed runtime div/mod
stages, rather than a second enumeration of the Fourier coefficients. -/

namespace Maxwell.Continuum.Calibration

open Maxwell.Cost FreeFiber
set_option maxHeartbeats 1500000

def decodedPolarization (i : ℕ) : ℕ := i % 3
def decodedCoordinates (R i : ℕ) : Fin 3 → ℕ :=
  ![i / 3 / (aliasSide R*aliasSide R), (i / 3 % (aliasSide R*aliasSide R)) / aliasSide R,
    (i / 3 % (aliasSide R*aliasSide R)) % aliasSide R]

theorem aliasArraySize_pos (R : ℕ) : 0 < aliasArraySize R := by
  unfold aliasArraySize aliasSide
  positivity

theorem arrayPolarizationAt_decode (R : ℕ) (i : Fin (aliasArraySize R)) :
    (arrayPolarizationAt R i).val=decodedPolarization i.val := by
  rfl

theorem arrayAliasAt_decode (R : ℕ) (i : Fin (aliasArraySize R)) (j : Fin 3) :
    arrayAliasAt R i j=(decodedCoordinates R i.val j : ℤ)-(R : ℤ) := by
  fin_cases j <;> rfl

theorem coordinatePart_decode (R : ℕ) (i : Fin (aliasArraySize R)) (j : Fin 3) :
    RawFree.coordinatePart R i j=⟨decodedCoordinates R i.val j,R,1⟩ := by
  fin_cases j <;> rfl

theorem decodedCoordinates_lt (R : ℕ) (i : Fin (aliasArraySize R)) (j : Fin 3) :
    decodedCoordinates R i.val j < aliasSide R := by
  let a := ((aliasArrayEquiv R).symm i).1
  fin_cases j
  · exact a.1.isLt
  · exact a.2.1.isLt
  · exact a.2.2.isLt

#print axioms coordinatePart_decode

end Maxwell.Continuum.Calibration
