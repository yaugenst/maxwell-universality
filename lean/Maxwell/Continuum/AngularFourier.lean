import Maxwell.Continuum.L2Dilation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The unitary angular-frequency Fourier transform on actual scalar or
Hilbert-valued L². The normalization is the manuscript's (2π)^(-3/2). -/

noncomputable section

namespace Maxwell.Continuum

open MeasureTheory FourierTransform

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def angularFourier : L2Dilation.L2 (H := H) ≃ₗᵢ[ℂ] L2Dilation.L2 (H := H) :=
  (Lp.fourierTransformₗᵢ Space H).trans
    (L2Dilation.equiv (a := 2 * Real.pi) (by positivity))

theorem angularFourier_factor : L2Dilation.factor (2 * Real.pi) =
    (2 * Real.pi) ^ (-(3 / 2 : ℝ)) := by
  rw [L2Dilation.factor, Real.sqrt_eq_rpow, ← Real.rpow_natCast_mul (by positivity),
    ← Real.rpow_neg (by positivity)]
  norm_num

theorem angularFourier_ae (u : L2Dilation.L2 (H := H)) :
    angularFourier H u =ᵐ[volume]
      fun p => (((2 * Real.pi) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) •
        (𝓕 u : L2Dilation.L2 (H := H)) ((2 * Real.pi)⁻¹ • p) := by
  have he := L2Dilation.equiv_ae (a := 2 * Real.pi) (by positivity) (𝓕 u)
  change L2Dilation.equiv (a := 2 * Real.pi) (by positivity) (𝓕 u) =ᵐ[volume] _
  simpa only [angularFourier_factor] using he

end Maxwell.Continuum
