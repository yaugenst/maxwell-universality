import Maxwell.Continuum.AlmostAnalyticReparameterization

/-! A contour can stop short of its limiting singular endpoint without
changing the cutoff truncation order. The same exponentially small
error controls every partial shift. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.AlmostAnalytic

open Complex FreeFiber PeriodicBand Auxiliary MasterConstants MeasureTheory Set Metric

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem partial_contour_integral_identity (K : ℕ) (β : Space) (Y : Momentum → F)
    {s : ℝ} (hs : 0 ≤ s)
    (hY : ∀ t ∈ Icc (0 : ℝ) s, ∀ q, ‖q‖ ≤ 4*smallRadius →
      AnalyticAt ℂ Y (shiftedMomentum q β t)) :
    (∫ q, contourProduct K β Y s q) - (∫ q, contourProduct K β Y 0 q) =
      ∫ t in (0 : ℝ)..1, (s : ℂ) • ∫ q, contourRemainder K β Y (s*t) q := by
  have ha : ∀ t ∈ Icc (0 : ℝ) 1, ∀ q, ‖q‖ ≤ 4*smallRadius →
      AnalyticAt ℂ Y (shiftedMomentum q (s • β) t) := by
    intro t ht q hq
    rw [shiftedMomentum_smul]
    exact hY (s*t) ⟨mul_nonneg hs ht.1, (mul_le_mul_of_nonneg_left ht.2 hs).trans_eq (mul_one s)⟩ q hq
  have he := contour_integral_identity K (s • β) Y ha
  simp_rw [contourProduct_smul, contourRemainder_smul, integral_smul] at he
  simpa only [mul_one, mul_zero] using he

theorem partial_contour_integral_error_bound {L : ℝ} (hL : Ls ≤ L) {β : Space}
    (hβ : ‖β‖ ≤ L⁻¹) (hβ0 : β ≠ 0) (Y : Momentum → F) {M s : ℝ}
    (hM : 0 ≤ M) (hs : s ∈ Icc (0 : ℝ) 1)
    (hYa : ∀ t ∈ Icc (0 : ℝ) s, ∀ q, ‖q‖ ≤ 4*smallRadius →
      AnalyticAt ℂ Y (shiftedMomentum q β t))
    (hYb : ∀ t ∈ Icc (0 : ℝ) s, ∀ q : Space, smallRadius ≤ ‖q‖ →
      ‖q‖ ≤ 4*smallRadius → ‖Y (shiftedMomentum q β t)‖ ≤ M) :
    ‖(∫ q, contourProduct (cutoffOrder β) β Y s q) -
      (∫ q, contourProduct (cutoffOrder β) β Y 0 q)‖ ≤
      (2 : ℝ)^49 * M * Real.exp (-cs*L) := by
  rw [partial_contour_integral_identity _ β Y hs.1 hYa]
  have hb : ∀ t ∈ uIoc (0 : ℝ) 1,
      ‖(s : ℂ) • ∫ q, contourRemainder (cutoffOrder β) β Y (s*t) q‖ ≤
        (2 : ℝ)^49 * M * Real.exp (-cs*L) := by
    intro t ht
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have hst : s*t ∈ Icc (0 : ℝ) s :=
      ⟨mul_nonneg hs.1 ht.1.le, (mul_le_mul_of_nonneg_left ht.2 hs.1).trans_eq (mul_one s)⟩
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
    have he := contourRemainder_integral_bound hL hβ hβ0 Y
      (show |s*t| ≤ 1 by rw [abs_of_nonneg hst.1]; exact hst.2.trans hs.2)
      hM (hYb (s*t) hst)
    exact (mul_le_mul_of_nonneg_left he hs.1).trans
      ((mul_le_mul_of_nonneg_right hs.2 (by positivity)).trans_eq (one_mul _))
  simpa only [sub_zero, abs_one, mul_one] using
    intervalIntegral.norm_integral_le_of_norm_le_const hb

#print axioms partial_contour_integral_error_bound

end Maxwell.Continuum.AlmostAnalytic
