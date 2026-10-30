import Maxwell.Continuum.CalibrationFiniteData
import Maxwell.Continuum.CalibrationFiniteNormalization

/-! Executable rational normalization preserving the concrete stored
Fourier array. No square root or Hilbert vector is used by the program. -/

namespace Maxwell.Continuum.Calibration.FourierData

open FreeFiber NormedSpace

def normCenter (P : ℕ) (v : FourierData) : ℚ := rationalNormCenter v.field v.radius P

def normalizeData (P : ℕ) (v : FourierData) : FourierData := scale (normCenter P v)⁻¹ v

theorem normCenter_error (P : ℕ) (v : FourierData) :
    |(normCenter P v : ℝ)-‖v.value‖| ≤ (1/2 : ℝ)^P :=
  rationalNormCenter_error v.supported v.represents P

theorem normalizeData_value (P : ℕ) (v : FourierData) :
    (normalizeData P v).value = (((normCenter P v)⁻¹ : ℚ) : ℂ) • v.value :=
  scale_value _ _

theorem normalizeData_error (P : ℕ) (v : FourierData)
    (hsmall : (1/2 : ℝ)^P ≤ ‖v.value‖/2) :
    0 < normCenter P v ∧
      ‖(normalizeData P v).value-normalize v.value‖ ≤ 2*(1/2 : ℝ)^P/‖v.value‖ := by
  have h := rationalNormalize_error v.supported v.represents P hsmall
  refine ⟨h.1,?_⟩
  rw [normalizeData_value]
  simpa only [Rat.cast_smul_eq_qsmul,normCenter] using h.2

#print axioms normalizeData_error

end Maxwell.Continuum.Calibration.FourierData
