import Maxwell.Continuum.FourierTranslation
import Maxwell.Continuum.BlochFreeSymbol
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.RealDeriv

/-! Literal Fourier difference quotients and their pointwise limits.
The 2π normalization agrees with the constructed Plancherel transform. -/

noncomputable section

namespace Maxwell.Continuum.FourierSobolev

open MeasureTheory FourierTransform Bloch Filter
open scoped Topology

def derivativeFactor (j : Fin 3) (ξ : Space) : ℂ :=
  2 * Real.pi * Complex.I * (ξ j : ℂ)

theorem derivativeFactor_continuous (j : Fin 3) : Continuous (derivativeFactor j) := by
  exact continuous_const.mul
    (Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 _ j))

theorem coordinateDirection_norm (j : Fin 3) : ‖coordinateDirection j‖ = 1 := by
  simp [coordinateDirection]

theorem coordinate_shift_norm (j : Fin 3) (t : ℝ) :
    ‖t • coordinateDirection j‖ = |t| := by
  rw [norm_smul, coordinateDirection_norm, mul_one, Real.norm_eq_abs]

theorem phase_coordinate (j : Fin 3) (t : ℝ) (ξ : Space) :
    phase (t • coordinateDirection j) ξ = Complex.exp ((t : ℂ) * derivativeFactor j ξ) := by
  simp only [phase, Real.fourierChar_apply, inner_smul_right, coordinateDirection,
    EuclideanSpace.inner_single_right]
  congr 1
  simp only [derivativeFactor]
  push_cast
  simp only [starRingEnd_apply, star_trivial]
  ring

def quotientFactor (j : Fin 3) (t : ℝ) (ξ : Space) : ℂ :=
  (t : ℂ)⁻¹ * (phase (t • coordinateDirection j) ξ - 1)

theorem quotientFactor_continuous (j : Fin 3) (t : ℝ) :
    Continuous (quotientFactor j t) :=
  continuous_const.mul ((phase_continuous _).sub continuous_const)

theorem quotientFactor_tendsto (j : Fin 3) (ξ : Space) :
    Tendsto (fun t : ℝ => quotientFactor j t ξ) (𝓝[≠] 0) (𝓝 (derivativeFactor j ξ)) := by
  have hd : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * derivativeFactor j ξ))
      (derivativeFactor j ξ) 0 := by
    simpa only [id_eq, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul] using
      (((hasDerivAt_id (0 : ℂ)).mul_const (derivativeFactor j ξ)).cexp.comp_ofReal)
  have ht := hd.tendsto_slope_zero
  simpa only [quotientFactor, phase_coordinate, zero_add, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, Complex.real_smul, Complex.ofReal_inv] using ht

def scalarQuotient (j : Fin 3) (t : ℝ) (f : ScalarL2) : ScalarL2 :=
  (t : ℂ)⁻¹ • (modulation (t • coordinateDirection j) (𝓕 f) - 𝓕 f)

theorem scalarQuotient_ae (j : Fin 3) (t : ℝ) (f : ScalarL2) :
    scalarQuotient j t f =ᵐ[volume] (fun ξ => quotientFactor j t ξ * 𝓕 f ξ) := by
  filter_upwards [Lp.coeFn_smul (t : ℂ)⁻¹
      (modulation (t • coordinateDirection j) (𝓕 f) - 𝓕 f),
    Lp.coeFn_sub (modulation (t • coordinateDirection j) (𝓕 f)) (𝓕 f),
    modulation_ae (t • coordinateDirection j) (𝓕 f)] with ξ hs hd hm
  change ((t : ℂ)⁻¹ • (modulation (t • coordinateDirection j) (𝓕 f) - 𝓕 f) : ScalarL2) ξ = _
  rw [hs]
  change (t : ℂ)⁻¹ * (modulation (t • coordinateDirection j) (𝓕 f) - 𝓕 f) ξ = _
  rw [hd]
  simp only [Pi.sub_apply, hm, quotientFactor]
  ring

theorem scalarQuotient_norm (j : Fin 3) (t : ℝ) (f : ScalarL2) :
    ‖scalarQuotient j t f‖ = |t|⁻¹ * ‖translation (t • coordinateDirection j) f - f‖ := by
  rw [scalarQuotient, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    ← fourier_translation]
  have he : 𝓕 (translation (t • coordinateDirection j) f) - 𝓕 f =
      𝓕 (translation (t • coordinateDirection j) f - f) :=
    (map_sub (Lp.fourierTransformₗᵢ Space ℂ) _ _).symm
  rw [he, Lp.norm_fourier_eq]

end Maxwell.Continuum.FourierSobolev
