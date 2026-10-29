import Maxwell.Continuum.PeriodicPhysicalHessian

/-! Real physical band curvature on the whole support of the auxiliary
cutoff. Every estimate concerns the actual infinite-dimensional band. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber

theorem norm_realMomentum_sq_le_dot (t : Corner.Vec) :
    ‖realMomentum t‖ ^ 2 ≤ dotProduct t t := by
  have hS := dot_self_nonneg t
  have hn : ‖realMomentum t‖ ≤ Real.sqrt (dotProduct t t) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro j
    simp only [realMomentum, Complex.norm_real, Real.norm_eq_abs]
    nlinarith [coordinate_sq_le_dot t j, Real.sq_sqrt hS,
      Real.sqrt_nonneg (dotProduct t t), abs_nonneg (t j), sq_abs (t j)]
  nlinarith [Real.sq_sqrt hS, Real.sqrt_nonneg (dotProduct t t),
    norm_nonneg (realMomentum t)]

theorem four_smallRadius_le_half : 4 * smallRadius ≤ analyticRadius / 2 := by
  unfold smallRadius analyticRadius
  have h := mul_le_mul_of_nonneg_left
    (by norm_num : 4 * ((2 : ℝ)^40)⁻¹ ≤ ((2 : ℝ)^12)⁻¹ / 2)
    backgroundAmplitude_pos.le
  nlinarith

theorem small_momentum_mem_physicalChart {q : Momentum}
    (hq : ‖q‖ ≤ 4 * smallRadius) : q ∈ physicalChart := by
  intro j
  exact lt_of_le_of_lt ((norm_le_pi_norm q j).trans (hq.trans four_smallRadius_le_half))
    (by linarith [analyticRadius_pos])

theorem dielectricBand_im_zero (t : Corner.Vec) (ht : realMomentum t ∈ physicalChart) :
    (dielectricBand (realMomentum t)).im = 0 := by
  have h := material_kernel_energy_im_zero t (dielectricBand (realMomentum t) + 7)
    backgroundAmplitude (dielectricBand_kernel ht)
  simpa using h

theorem dielectricBand_ofReal_re (t : Corner.Vec) (ht : realMomentum t ∈ physicalChart) :
    ((dielectricBand (realMomentum t)).re : ℂ) = dielectricBand (realMomentum t) := by
  apply Complex.ext
  · simp
  · simp [dielectricBand_im_zero t ht]

theorem quarticConstant_nonneg : 0 ≤ quarticConstant := by
  have hρ := backgroundAmplitude_pos
  unfold quarticConstant
  positivity

theorem small_quartic_factor :
    quarticConstant * (4 * smallRadius)^2 ≤ (4 * backgroundAmplitude)⁻¹ := by
  norm_num [quarticConstant, smallRadius, analyticRadius, backgroundAmplitude]

theorem physical_small_remainder (t : Corner.Vec)
    (ht : ‖realMomentum t‖ ≤ 4 * smallRadius) :
    ‖dielectricBand (realMomentum t) - dielectricBand 0 -
      physicalQuadratic (realMomentum t)‖ ≤
        (4 * backgroundAmplitude)⁻¹ * dotProduct t t := by
  have hn := norm_nonneg (realMomentum t)
  have hr : 0 ≤ 4 * smallRadius := mul_nonneg (by norm_num) smallRadius_pos.le
  have h2 : ‖realMomentum t‖ ^ 2 ≤ (4 * smallRadius)^2 := by nlinarith
  have h4 : ‖realMomentum t‖ ^ 4 ≤ (4 * smallRadius)^2 * ‖realMomentum t‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖realMomentum t‖)]
  calc
    _ ≤ quarticConstant * ‖realMomentum t‖ ^ 4 :=
      physical_quartic (ht.trans four_smallRadius_le_half)
    _ ≤ quarticConstant * ((4 * smallRadius)^2 * ‖realMomentum t‖ ^ 2) :=
      mul_le_mul_of_nonneg_left h4 quarticConstant_nonneg
    _ = (quarticConstant * (4 * smallRadius)^2) * ‖realMomentum t‖ ^ 2 := by ring
    _ ≤ (4 * backgroundAmplitude)⁻¹ * ‖realMomentum t‖ ^ 2 :=
      mul_le_mul_of_nonneg_right small_quartic_factor (sq_nonneg _)
    _ ≤ (4 * backgroundAmplitude)⁻¹ * dotProduct t t :=
      mul_le_mul_of_nonneg_left (norm_realMomentum_sq_le_dot t)
        (inv_nonneg.mpr (mul_nonneg (by norm_num) backgroundAmplitude_pos.le))

/-- The true band rises quadratically throughout the cutoff chart. -/
theorem physical_small_curvature (t : Corner.Vec)
    (ht : ‖realMomentum t‖ ≤ 4 * smallRadius) :
    (1 / 2 : ℝ) * dotProduct t (hessian.mulVec t) ≤
        (dielectricBand (realMomentum t)).re - (dielectricBand 0).re ∧
      (dielectricBand (realMomentum t)).re - (dielectricBand 0).re ≤
        (3 / 2 : ℝ) * dotProduct t (hessian.mulVec t) := by
  have herr := (Complex.abs_re_le_norm
    (dielectricBand (realMomentum t) - dielectricBand 0 -
      physicalQuadratic (realMomentum t))).trans (physical_small_remainder t ht)
  rw [physicalQuadratic_real_form] at herr
  simp only [Complex.sub_re, Complex.ofReal_re] at herr
  have hq := (hessian_bounds t).1
  have hid : (4 * backgroundAmplitude)⁻¹ =
      (1 / 2 : ℝ) * (2 * backgroundAmplitude)⁻¹ := by ring
  rw [hid] at herr
  obtain ⟨hlo, hhi⟩ := abs_le.mp herr
  constructor <;> nlinarith

end Maxwell.Continuum.PeriodicBand
