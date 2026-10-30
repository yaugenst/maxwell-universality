import Maxwell.Continuum.PeriodicShiftedCurvatureEven

/-! Real curvature of the literal band remains positive about every
small imaginary center. The error is proved from the convergent even
Taylor series of its symmetrized quartic remainder. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary

attribute [local irreducible] dielectricBand hessianEnergy physicalRemainder

theorem shifted_remainder_coefficient_le :
    2 * (quarticConstant * (9 * smallRadius)^4) / (8 * smallRadius)^2 ≤
      (2 * backgroundAmplitude)⁻¹ / 2 := by
  norm_num [quarticConstant, smallRadius, analyticRadius, backgroundAmplitude]

theorem shifted_band_curvature_error (q b : Corner.Vec)
    (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) (hb : ‖realMomentum b‖ ≤ smallRadius) :
    |(dielectricBand (shiftedMomentum q b)).re -
      (dielectricBand (shiftedMomentum 0 b)).re - hessianEnergy q| ≤ hessianEnergy q / 2 := by
  by_cases hq0 : q = 0
  · subst q
    rw [hessianEnergy_zero]
    simp
  have hqn : realMomentum q ≠ 0 := by
    intro he
    apply hq0
    funext j
    exact Complex.ofReal_injective (congrFun he j)
  have hn : 0 < ‖realMomentum q‖ := norm_pos_iff.mpr hqn
  let a : Momentum := ((‖realMomentum q‖ : ℝ) : ℂ)⁻¹ • realMomentum q
  let c : Momentum := Complex.I • realMomentum b
  have ha : ‖a‖ = 1 := by
    simp only [a, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hn, inv_mul_cancel₀ hn.ne']
  have hc : ‖c‖ ≤ smallRadius := by
    simpa only [c, norm_smul, Complex.norm_I, one_mul] using hb
  have hr : ((‖realMomentum q‖ : ℝ) : ℂ) • a = realMomentum q := by
    dsimp only [a]
    rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hn.ne'), one_smul]
  have hrn : (-((‖realMomentum q‖ : ℝ) : ℂ)) • a = realMomentum (-q) := by
    rw [neg_smul, hr]
    funext j
    simp only [Pi.neg_apply, realMomentum, Complex.ofReal_neg]
  have hz : ‖((‖realMomentum q‖ : ℝ) : ℂ)‖ ≤ 4 * smallRadius := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn] using hq
  have hp : shiftedMomentum q b ∈ physicalChart := by
    change realMomentum q + c ∈ physicalChart
    rw [← hr]
    exact small_center_line_chart a c ha hc (lt_of_le_of_lt hz (by linarith [smallRadius_pos]))
  have hsym : (symmetrizedRemainder a c ((‖realMomentum q‖ : ℝ) : ℂ) -
      physicalRemainder c).re =
      (physicalRemainder (shiftedMomentum q b) - physicalRemainder (shiftedMomentum 0 b)).re := by
    unfold symmetrizedRemainder
    rw [hr, hrn]
    have hc0 : c = shiftedMomentum 0 b := by
      funext j
      simp [c, shiftedMomentum, realMomentum]
    change ((physicalRemainder (shiftedMomentum q b) +
      physicalRemainder (shiftedMomentum (-q) b)) / 2 - physicalRemainder c).re = _
    rw [hc0]
    simp only [Complex.sub_re, Complex.div_re, Complex.add_re,
      physicalRemainder_shift_re_neg q b hp]
    norm_num
    ring
  have he := (Complex.abs_re_le_norm _).trans
    (symmetrizedRemainder_difference a c ha hc hz)
  rw [hsym, physicalRemainder_shift_difference_re] at he
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn] at he
  calc
    _ ≤ (2 * (quarticConstant * (9 * smallRadius)^4) / (8 * smallRadius)^2) *
        ‖realMomentum q‖^2 := he
    _ ≤ ((2 * backgroundAmplitude)⁻¹ / 2) * ‖realMomentum q‖^2 :=
      mul_le_mul_of_nonneg_right shifted_remainder_coefficient_le (sq_nonneg _)
    _ = ((2 * backgroundAmplitude)⁻¹ * ‖realMomentum q‖^2) / 2 := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (hessianEnergy_lower q) (by norm_num)

theorem shifted_band_curvature_lower (q b : Corner.Vec)
    (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) (hb : ‖realMomentum b‖ ≤ smallRadius) :
    hessianEnergy q / 2 ≤ (dielectricBand (shiftedMomentum q b)).re -
      (dielectricBand (shiftedMomentum 0 b)).re := by
  have he := (abs_le.mp (shifted_band_curvature_error q b hq hb)).1
  linarith

end Maxwell.Continuum.PeriodicBand
