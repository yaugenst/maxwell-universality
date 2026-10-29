import Maxwell.Continuum.EffectiveMassDenominator
import Maxwell.Continuum.SquareRootStability

/-! Uniform reference-multiplier estimates with the actual Hessian. -/

noncomputable section

namespace Maxwell.Continuum.EffectiveMass

open FreeFiber PeriodicBand Auxiliary

def referenceMultiplier (p : Space) : ℝ := (Real.sqrt (referenceDenominator p))⁻¹

def bandMultiplier (h z : ℝ) (p : Space) : ℝ := (Real.sqrt (bandDenominator h z p))⁻¹

theorem referenceDenominator_pos (p : Space) : 0 < referenceDenominator p :=
  lt_of_lt_of_le zero_lt_one (referenceDenominator_ge_one p)

theorem referenceDenominator_lower (p : Space) :
    (2 : ℝ)^98 * ‖p‖^2 ≤ referenceDenominator p := by
  have h := (hessianOperator_bounds p).1
  have hc : (2 : ℝ)^98 ≤ (2 * backgroundAmplitude)⁻¹ := by
    norm_num [backgroundAmplitude]
  have hh := mul_le_mul_of_nonneg_right hc (sq_nonneg ‖p‖)
  change (2 : ℝ)^98 * ‖p‖^2 ≤ 1 + quadratic p
  change (2 * backgroundAmplitude)⁻¹ * ‖p‖^2 ≤ quadratic p at h
  linarith

theorem referenceSqrt_ge_one (p : Space) : 1 ≤ Real.sqrt (referenceDenominator p) := by
  nlinarith [Real.sq_sqrt (referenceDenominator_pos p).le,
    Real.sqrt_nonneg (referenceDenominator p), referenceDenominator_ge_one p]

theorem referenceSqrt_lower (p : Space) :
    (2 : ℝ)^49 * ‖p‖ ≤ Real.sqrt (referenceDenominator p) := by
  have h := referenceDenominator_lower p
  have hs := Real.sq_sqrt (referenceDenominator_pos p).le
  have hn := Real.sqrt_nonneg (referenceDenominator p)
  nlinarith [norm_nonneg p]

theorem referenceMultiplier_nonneg (p : Space) : 0 ≤ referenceMultiplier p := by
  unfold referenceMultiplier
  positivity

theorem referenceMultiplier_le_one (p : Space) : referenceMultiplier p ≤ 1 :=
  inv_le_one_of_one_le₀ (referenceSqrt_ge_one p)

theorem referenceMultiplier_weighted (p : Space) :
    ‖p‖ * referenceMultiplier p ≤ ((2 : ℝ)^49)⁻¹ := by
  unfold referenceMultiplier
  rw [← div_eq_mul_inv, div_le_iff₀ (Real.sqrt_pos.mpr (referenceDenominator_pos p))]
  have h := mul_le_mul_of_nonneg_left (referenceSqrt_lower p)
    (show 0 ≤ ((2 : ℝ)^49)⁻¹ by positivity)
  norm_num at h ⊢
  linarith

theorem referenceCube_ge_one (p : Space) :
    1 ≤ referenceDenominator p * Real.sqrt (referenceDenominator p) := by
  nlinarith [referenceDenominator_ge_one p, referenceSqrt_ge_one p]

theorem referenceCube_lower (p : Space) :
    (2 : ℝ)^147 * ‖p‖^3 ≤
      referenceDenominator p * Real.sqrt (referenceDenominator p) := by
  calc
    _ = ((2 : ℝ)^98 * ‖p‖^2) * ((2 : ℝ)^49 * ‖p‖) := by ring
    _ ≤ _ := mul_le_mul (referenceDenominator_lower p) (referenceSqrt_lower p)
      (by positivity) (referenceDenominator_pos p).le

theorem quartic_reference_ratio (p : Space) :
    ‖p‖^4 / (referenceDenominator p * Real.sqrt (referenceDenominator p)) ≤
      ‖p‖ / (2 : ℝ)^147 := by
  apply (div_le_div_iff₀
    (mul_pos (referenceDenominator_pos p) (Real.sqrt_pos.mpr (referenceDenominator_pos p)))
    (by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_right (referenceCube_lower p) (norm_nonneg p)]

end Maxwell.Continuum.EffectiveMass
