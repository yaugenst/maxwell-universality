import Maxwell.Continuum.PeriodicComplexQuadratic
import Maxwell.Continuum.PeriodicImaginaryDerivative

/-! The selected-band denominator on the actual imaginary tube. The
positive lower bound includes the literal quartic remainder, calibration
error and allowed detuning. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary

attribute [local irreducible] dielectricBand hessianEnergy shiftedMomentum realMomentum

theorem tube_shift_norm_le {h : ℝ} (h0 : 0 ≤ h) (b : Corner.Vec)
    (hb : hessianEnergy b ≤ (99 / 100 : ℝ)^2 * h^2) : ‖realMomentum b‖ ≤ h := by
  have hl := norm_sq_le_hessianEnergy b
  nlinarith [norm_nonneg (realMomentum b), sq_nonneg h]

theorem tube_chart_radius {h : ℝ} (h0 : 0 ≤ h)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (q b : Corner.Vec)
    (hq : ‖realMomentum q‖ ≤ 4 * smallRadius)
    (hb : hessianEnergy b ≤ (99 / 100 : ℝ)^2 * h^2) :
    ‖shiftedMomentum q b‖ ≤ analyticRadius / 2 := by
  have hbn := tube_shift_norm_le h0 b hb
  calc
    _ ≤ ‖realMomentum q‖ + ‖realMomentum b‖ := shiftedMomentum_norm_le q b
    _ ≤ 4 * smallRadius + 1 / (2 : ℝ)^1024 := add_le_add hq (hbn.trans hh)
    _ ≤ _ := by norm_num [smallRadius, analyticRadius, backgroundAmplitude]

theorem tube_quartic_real_constant :
    8 * quarticConstant * (4 * smallRadius)^2 ≤ (2 * backgroundAmplitude)⁻¹ / 1000 := by
  norm_num [quarticConstant, smallRadius, analyticRadius, backgroundAmplitude]

theorem tube_real_quartic (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) :
    8 * quarticConstant * ‖realMomentum q‖^4 ≤ hessianEnergy q / 1000 := by
  have hc := quarticConstant_nonneg
  have hs := pow_le_pow_left₀ (norm_nonneg (realMomentum q)) hq 2
  have h4 : ‖realMomentum q‖^4 ≤ (4 * smallRadius)^2 * ‖realMomentum q‖^2 := by
    nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg ‖realMomentum q‖)]
  calc
    _ ≤ 8 * quarticConstant * ((4 * smallRadius)^2 * ‖realMomentum q‖^2) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = (8 * quarticConstant * (4 * smallRadius)^2) * ‖realMomentum q‖^2 := by ring
    _ ≤ ((2 * backgroundAmplitude)⁻¹ / 1000) * ‖realMomentum q‖^2 :=
      mul_le_mul_of_nonneg_right tube_quartic_real_constant (sq_nonneg _)
    _ = ((2 * backgroundAmplitude)⁻¹ * ‖realMomentum q‖^2) / 1000 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (hessianEnergy_lower q) (by norm_num)

theorem tube_imaginary_quartic {h : ℝ} (h0 : 0 ≤ h)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (b : Corner.Vec)
    (hb : hessianEnergy b ≤ (99 / 100 : ℝ)^2 * h^2) :
    8 * quarticConstant * ‖realMomentum b‖^4 ≤ h^2 / 1000 := by
  have hc := quarticConstant_nonneg
  have hs := (imaginary_scale_bounds h0 hh).2.2.1
  have hn := tube_shift_norm_le h0 b hb
  have hp : 8 * quarticConstant * h^4 ≤ h^2 / 1000 := by
    nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg h),
      mul_nonneg hc (pow_nonneg h0 4)]
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn 4)
    (by positivity : 0 ≤ 8 * quarticConstant)).trans hp

theorem tube_remainder_norm {h : ℝ} (h0 : 0 ≤ h)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (q b : Corner.Vec)
    (hq : ‖realMomentum q‖ ≤ 4 * smallRadius)
    (hb : hessianEnergy b ≤ (99 / 100 : ℝ)^2 * h^2) :
    ‖dielectricBand (shiftedMomentum q b) - dielectricBand 0 -
      physicalQuadratic (shiftedMomentum q b)‖ ≤ (h^2 + hessianEnergy q) / 1000 := by
  have hc := quarticConstant_nonneg
  calc
    _ ≤ quarticConstant * ‖shiftedMomentum q b‖^4 :=
      physical_quartic (tube_chart_radius h0 hh q b hq hb)
    _ ≤ quarticConstant * (8 * (‖realMomentum q‖^4 + ‖realMomentum b‖^4)) :=
      mul_le_mul_of_nonneg_left (shiftedMomentum_norm_fourth q b) hc
    _ = 8 * quarticConstant * ‖realMomentum q‖^4 +
        8 * quarticConstant * ‖realMomentum b‖^4 := by ring
    _ ≤ hessianEnergy q / 1000 + h^2 / 1000 :=
      add_le_add (tube_real_quartic q hq) (tube_imaginary_quartic h0 hh b hb)
    _ = _ := by ring

theorem tube_remainder_re {h : ℝ} (h0 : 0 ≤ h)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (q b : Corner.Vec)
    (hq : ‖realMomentum q‖ ≤ 4 * smallRadius)
    (hb : hessianEnergy b ≤ (99 / 100 : ℝ)^2 * h^2) :
    |(dielectricBand (shiftedMomentum q b)).re - centerEnergy -
      (hessianEnergy q - hessianEnergy b)| ≤ (h^2 + hessianEnergy q) / 1000 := by
  have he := (Complex.abs_re_le_norm _).trans (tube_remainder_norm h0 hh q b hq hb)
  simpa only [Complex.sub_re, shifted_quadratic_re, centerEnergy] using he

theorem tube_numeric_lower {a E z σ Q B h : ℝ} (hQ : 0 ≤ Q)
    (hB : B ≤ (99 / 100 : ℝ)^2 * h^2)
    (hz : z - (E - h^2) ≤ h^4) (hσ : σ ≤ h^4 / 64)
    (h4 : h^4 ≤ h^2 / 1000)
    (he : |a - E - (Q - B)| ≤ (h^2 + Q) / 1000) :
    (1 / 256 : ℝ) * (h^2 + Q) ≤ a - (z + σ) := by
  have hl := (abs_le.mp he).1
  nlinarith [sq_nonneg h]

theorem tube_denominator_lower {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ : σ ≤ h^4 / 64) (q b : Corner.Vec)
    (hq : ‖realMomentum q‖ ≤ 4 * smallRadius)
    (hb : hessianEnergy b ≤ (99 / 100 : ℝ)^2 * h^2) :
    (1 / 256 : ℝ) * (h^2 + hessianEnergy q) ≤
      (dielectricBand (shiftedMomentum q b) - ((z + σ : ℝ) : ℂ)).re := by
  have hs := (imaginary_scale_bounds D.h_pos.le hh).2.2.2
  have h4 : h^4 ≤ h^2 / 1000 := by
    nlinarith [mul_le_mul_of_nonneg_right hs (sq_nonneg h)]
  simpa only [Complex.sub_re, Complex.ofReal_re] using
    tube_numeric_lower (hessianEnergy_nonneg q) hb (abs_le.mp D.error).2 hσ h4
      (tube_remainder_re D.h_pos.le hh q b hq hb)

theorem tube_denominator_ne_zero {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ : σ ≤ h^4 / 64) (q b : Corner.Vec)
    (hq : ‖realMomentum q‖ ≤ 4 * smallRadius)
    (hb : hessianEnergy b ≤ (99 / 100 : ℝ)^2 * h^2) :
    dielectricBand (shiftedMomentum q b) - ((z + σ : ℝ) : ℂ) ≠ 0 := by
  intro he
  have hl := tube_denominator_lower D hh hσ q b hq hb
  rw [he, Complex.zero_re] at hl
  have hp := mul_pos (by norm_num : (0 : ℝ) < 1/256)
    (add_pos_of_pos_of_nonneg (sq_pos_of_pos D.h_pos) (hessianEnergy_nonneg q))
  exact not_le_of_gt hp hl

theorem tube_inverse_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ : σ ≤ h^4 / 64) (q b : Corner.Vec)
    (hq : ‖realMomentum q‖ ≤ 4 * smallRadius)
    (hb : hessianEnergy b ≤ (99 / 100 : ℝ)^2 * h^2) :
    ‖(dielectricBand (shiftedMomentum q b) - ((z + σ : ℝ) : ℂ))⁻¹‖ ≤
      256 * (h^2)⁻¹ := by
  have hne := tube_denominator_ne_zero D hh hσ q b hq hb
  have hl : h^2 / 256 ≤ ‖dielectricBand (shiftedMomentum q b) - ((z + σ : ℝ) : ℂ)‖ := by
    calc
      _ = (1 / 256 : ℝ) * h^2 := by ring
      _ ≤ (1 / 256 : ℝ) * (h^2 + hessianEnergy q) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (hessianEnergy_nonneg q)) (by norm_num)
      _ ≤ (dielectricBand (shiftedMomentum q b) - ((z + σ : ℝ) : ℂ)).re :=
        tube_denominator_lower D hh hσ q b hq hb
      _ ≤ _ := Complex.re_le_norm _
  rw [norm_inv]
  have hi := (inv_le_inv₀ (norm_pos_iff.mpr hne)
    (div_pos (sq_pos_of_pos D.h_pos) (by norm_num))).mpr hl
  exact hi.trans_eq (by rw [div_eq_mul_inv, mul_inv_rev, inv_inv])

end Maxwell.Continuum.PeriodicBand
