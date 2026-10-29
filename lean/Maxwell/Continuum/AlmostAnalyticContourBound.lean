import Maxwell.Continuum.AlmostAnalyticContourIntegral

/-! Quantitative contour movement with the literal Gevrey cutoff.
The error is supported on the fixed transition shell, so only the
symbol bound on that shell enters the estimate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.AlmostAnalytic

open Complex FreeFiber PeriodicBand Auxiliary MasterConstants MeasureTheory Set Metric

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem cutoffDefect_norm_le {L : ℝ} (hL : Ls ≤ L) {β : Space}
    (hβ : ‖β‖ ≤ L⁻¹) (hβ0 : β ≠ 0) (q : Space) {s : ℝ} (hs : |s| ≤ 1) :
    ‖cutoffDefect (cutoffOrder β) β s q‖ ≤ (2 : ℝ)^46 * Real.exp (-cs*L) := by
  have he := cutoffTaylor_error_small hL hβ hβ0 q hs
  rw [cutoffTaylor_defect] at he
  exact he

omit [CompleteSpace F] in
theorem contourRemainder_integral_bound {L : ℝ} (hL : Ls ≤ L) {β : Space}
    (hβ : ‖β‖ ≤ L⁻¹) (hβ0 : β ≠ 0) (Y : Momentum → F)
    {s M : ℝ} (hs : |s| ≤ 1) (hM : 0 ≤ M)
    (hY : ∀ q : Space, smallRadius ≤ ‖q‖ → ‖q‖ ≤ 4*smallRadius →
      ‖Y (shiftedMomentum q β s)‖ ≤ M) :
    ‖∫ q, contourRemainder (cutoffOrder β) β Y s q‖ ≤
      (2 : ℝ)^49 * M * Real.exp (-cs*L) := by
  have hsmall : 4*smallRadius ≤ (1 : ℝ) := by
    norm_num [smallRadius, backgroundAmplitude]
  have hsupp : Function.support (contourRemainder (cutoffOrder β) β Y s) ⊆
      closedBall (0 : Space) 1 := by
    intro q hq
    have hd : cutoffDefect (cutoffOrder β) β s q ≠ 0 := by
      intro hz
      apply Function.mem_support.mp hq
      rw [contourRemainder, hz, zero_smul]
    have hb := cutoffDefect_tsupport (cutoffOrder β) β s (subset_closure hd)
    simpa only [mem_closedBall, dist_zero_right] using hb.2.trans hsmall
  have hbound (q : Space) : ‖contourRemainder (cutoffOrder β) β Y s q‖ ≤
      ((2 : ℝ)^46 * Real.exp (-cs*L))*M := by
    by_cases hz : cutoffDefect (cutoffOrder β) β s q = 0
    · simp only [contourRemainder, hz, zero_smul, norm_zero]
      positivity
    · have hb := cutoffDefect_tsupport (cutoffOrder β) β s (subset_closure hz)
      rw [contourRemainder, norm_smul]
      exact mul_le_mul (cutoffDefect_norm_le hL hβ hβ0 q hs)
        (hY q hb.1 hb.2) (norm_nonneg _) (by positivity)
  apply (integral_norm_compact_le _ (by positivity) hsupp hbound).trans_eq
  ring

theorem contour_integral_error_bound {L : ℝ} (hL : Ls ≤ L) {β : Space}
    (hβ : ‖β‖ ≤ L⁻¹) (hβ0 : β ≠ 0) (Y : Momentum → F) {M : ℝ} (hM : 0 ≤ M)
    (hYa : ∀ s ∈ Icc (0 : ℝ) 1, ∀ q, ‖q‖ ≤ 4*smallRadius →
      AnalyticAt ℂ Y (shiftedMomentum q β s))
    (hYb : ∀ s ∈ Icc (0 : ℝ) 1, ∀ q : Space, smallRadius ≤ ‖q‖ →
      ‖q‖ ≤ 4*smallRadius → ‖Y (shiftedMomentum q β s)‖ ≤ M) :
    ‖(∫ q, contourProduct (cutoffOrder β) β Y 1 q) -
      (∫ q, contourProduct (cutoffOrder β) β Y 0 q)‖ ≤
      (2 : ℝ)^49 * M * Real.exp (-cs*L) := by
  rw [contour_integral_identity _ β Y hYa]
  have hb : ∀ s ∈ uIoc (0 : ℝ) 1,
      ‖∫ q, contourRemainder (cutoffOrder β) β Y s q‖ ≤
        (2 : ℝ)^49 * M * Real.exp (-cs*L) := by
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) 1 := by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
      exact ⟨hs.1.le, hs.2⟩
    exact contourRemainder_integral_bound hL hβ hβ0 Y
      (abs_le.mpr ⟨by linarith only [hs'.1], hs'.2⟩) hM (hYb s hs')
  simpa only [sub_zero, abs_one, mul_one] using
    intervalIntegral.norm_integral_le_of_norm_le_const hb

#print axioms contour_integral_error_bound

end Maxwell.Continuum.AlmostAnalytic
