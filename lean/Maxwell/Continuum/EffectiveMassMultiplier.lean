import Maxwell.Continuum.EffectiveMassReference

/-! The inverse-square-root multiplier of the actual continuum band
approaches the effective elliptic multiplier uniformly with explicit O(h). -/

noncomputable section

namespace Maxwell.Continuum.EffectiveMass

open FreeFiber PeriodicBand Auxiliary

theorem small_chart_quartic_constant :
    2 * quarticConstant * (4 * smallRadius) / (2 : ℝ)^147 ≤ (2 : ℝ)^70 := by
  norm_num [quarticConstant, smallRadius, analyticRadius, backgroundAmplitude]

theorem multiplier_error_majorant {h z : ℝ} (D : Calibration h z)
    (p : Space) (hp : h * ‖p‖ ≤ 4 * smallRadius) :
    2 * (h^2 * (1 + quarticConstant * ‖p‖^4)) /
      (referenceDenominator p * Real.sqrt (referenceDenominator p)) ≤ (2 : ℝ)^100 * h := by
  let d := referenceDenominator p * Real.sqrt (referenceDenominator p)
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one (referenceCube_ge_one p)
  have hh0 := D.h_pos
  have hh := calibration_h_small D
  have hh2 : h^2 ≤ h := by nlinarith [D.h_pos]
  have hc0 := quarticConstant_nonneg
  have hconst : 2 * h^2 / d ≤ 2 * h := by
    apply (div_le_iff₀ hd).mpr
    nlinarith [mul_le_mul_of_nonneg_left (referenceCube_ge_one p)
      (show 0 ≤ 2 * h by linarith [D.h_pos])]
  have htail : 2 * h^2 * quarticConstant * (‖p‖ / (2 : ℝ)^147) ≤ (2 : ℝ)^70 * h := by
    calc
      _ = (h * (2 * quarticConstant / (2 : ℝ)^147)) * (h * ‖p‖) := by ring
      _ ≤ (h * (2 * quarticConstant / (2 : ℝ)^147)) * (4 * smallRadius) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = h * (2 * quarticConstant * (4 * smallRadius) / (2 : ℝ)^147) := by ring
      _ ≤ h * (2 : ℝ)^70 := mul_le_mul_of_nonneg_left small_chart_quartic_constant D.h_pos.le
      _ = (2 : ℝ)^70 * h := by ring
  calc
    _ = 2 * h^2 / d + 2 * h^2 * quarticConstant * (‖p‖^4 / d) := by dsimp [d]; ring
    _ ≤ 2 * h + 2 * h^2 * quarticConstant * (‖p‖ / (2 : ℝ)^147) :=
      add_le_add hconst (mul_le_mul_of_nonneg_left (quartic_reference_ratio p) (by positivity))
    _ ≤ 2 * h + (2 : ℝ)^70 * h := add_le_add le_rfl htail
    _ ≤ (2 : ℝ)^100 * h := by nlinarith [D.h_pos]

theorem bandMultiplier_error {h z : ℝ} (D : Calibration h z)
    (p : Space) (hp : h * ‖p‖ ≤ 4 * smallRadius) :
    |bandMultiplier h z p - referenceMultiplier p| ≤ (2 : ℝ)^100 * h := by
  have hbound := inv_sqrt_sub_bound (referenceDenominator_pos p) (bandDenominator_lower D p hp)
  change |bandMultiplier h z p - referenceMultiplier p| ≤ _ at hbound
  calc
    _ ≤ 2 * |bandDenominator h z p - referenceDenominator p| /
        (referenceDenominator p * Real.sqrt (referenceDenominator p)) := hbound
    _ ≤ 2 * (h^2 * (1 + quarticConstant * ‖p‖^4)) /
        (referenceDenominator p * Real.sqrt (referenceDenominator p)) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (bandDenominator_error D p hp) (by norm_num))
        (mul_nonneg (referenceDenominator_pos p).le (Real.sqrt_nonneg _))
    _ ≤ (2 : ℝ)^100 * h := multiplier_error_majorant D p hp

theorem bandMultiplier_physical {h z : ℝ} (D : Calibration h z)
    (p : Space) : bandMultiplier h z p = h / Real.sqrt (bandValue (h • p) - z) := by
  rw [bandMultiplier, bandDenominator, Real.sqrt_div' _ (sq_nonneg h),
    Real.sqrt_sq_eq_abs, abs_of_pos D.h_pos, inv_div]

end Maxwell.Continuum.EffectiveMass
