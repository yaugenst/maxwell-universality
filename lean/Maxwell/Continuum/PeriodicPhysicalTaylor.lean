import Maxwell.Continuum.PeriodicPhysicalBand

/-! The fourth-order physical band expansion, with the exact displayed
constant. Its quadratic term is the proved actual Hessian coefficient. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber

def physicalQuadratic (q : Momentum) : ℂ :=
  (backgroundAmplitude : ℂ)⁻¹ * bandQuadratic q

theorem unscale_line (t : Momentum) (z : ℂ) :
    unscale (z • t) = (z / (backgroundAmplitude : ℂ)) • t := by
  unfold unscale
  rw [smul_smul]
  congr 1
  ring

theorem physical_remainder_line_identity (t : Momentum) (z : ℂ) :
    dielectricBand (z • t) - dielectricBand 0 - physicalQuadratic (z • t) =
      (backgroundAmplitude : ℂ) *
        (scaledSlice t (z / (backgroundAmplitude : ℂ)) - scaledBand 0 -
          bandQuadratic t * (z / (backgroundAmplitude : ℂ)) ^ 2) := by
  have hρ : (backgroundAmplitude : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr backgroundAmplitude_pos.ne'
  rw [dielectricBand_formula, dielectricBand_formula, physicalQuadratic,
    bandQuadratic_smul, unscale_line]
  simp only [unscale, smul_zero, scaledSlice]
  field_simp
  ring

theorem physical_line_quartic {t : Momentum} (ht : ∀ j, ‖t j‖ ≤ 1)
    {z : ℂ} (hz : ‖z‖ ≤ analyticRadius / 2) :
    ‖dielectricBand (z • t) - dielectricBand 0 - physicalQuadratic (z • t)‖ ≤
      quarticConstant * ‖z‖ ^ 4 := by
  have hnorm : ‖z / (backgroundAmplitude : ℂ)‖ = ‖z‖ / backgroundAmplitude := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos backgroundAmplitude_pos]
  have hz' : ‖z / (backgroundAmplitude : ℂ)‖ ≤ ((2 : ℝ)^12)⁻¹ / 2 := by
    rw [hnorm]
    apply (div_le_iff₀ backgroundAmplitude_pos).mpr
    change ‖z‖ ≤ backgroundAmplitude * ((2 : ℝ)^12)⁻¹ / 2 at hz
    nlinarith
  have h := scaledSlice_quartic ht hz'
  rw [← bandQuadratic_eq_coefficient, hnorm] at h
  rw [physical_remainder_line_identity, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos backgroundAmplitude_pos]
  refine (mul_le_mul_of_nonneg_left h backgroundAmplitude_pos.le).trans_eq ?_
  unfold quarticConstant analyticRadius
  field_simp [backgroundAmplitude_pos.ne']

/-- A stronger sup-norm version of the paper's Euclidean quartic bound. -/
theorem physical_quartic {q : Momentum} (hq : ‖q‖ ≤ analyticRadius / 2) :
    ‖dielectricBand q - dielectricBand 0 - physicalQuadratic q‖ ≤
      quarticConstant * ‖q‖ ^ 4 := by
  by_cases hq0 : q = 0
  · subst q
    simp [physicalQuadratic, bandQuadratic_zero]
  have hn : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  let t : Momentum := ((‖q‖ : ℝ) : ℂ)⁻¹ • q
  have ht : ∀ j, ‖t j‖ ≤ 1 := by
    intro j
    change ‖((‖q‖ : ℝ) : ℂ)⁻¹ * q j‖ ≤ 1
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn]
    exact (mul_le_mul_of_nonneg_left (norm_le_pi_norm q j) (inv_nonneg.mpr hn.le)).trans_eq
      (inv_mul_cancel₀ hn.ne')
  have hrec : ((‖q‖ : ℝ) : ℂ) • t = q := by
    dsimp only [t]
    rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hn.ne'), one_smul]
  have h := physical_line_quartic ht (z := ((‖q‖ : ℝ) : ℂ)) (by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn] using hq)
  simpa only [hrec, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn] using h

theorem physical_small_chart_quartic {q : Momentum} (hq : ‖q‖ ≤ smallRadius) :
    ‖dielectricBand q - dielectricBand 0 - physicalQuadratic q‖ ≤
      quarticConstant * ‖q‖ ^ 4 :=
  physical_quartic (hq.trans smallRadius_le_half)

end Maxwell.Continuum.PeriodicBand
