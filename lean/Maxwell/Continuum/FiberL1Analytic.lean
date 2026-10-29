import Maxwell.Continuum.FiberL1Cauchy
import Maxwell.Continuum.FiberL1Space
import Mathlib.Analysis.Complex.HasPrimitives

/-! Holomorphic lifting from the actual ℓ² fiber to its full ℓ¹ Fourier
space. Local ℓ¹ boundedness first gives continuity by finite-functional
Cauchy estimates; Morera then gives genuine ℓ¹ analyticity. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiberL1

open Set Metric MeasureTheory Complex
open scoped Topology

theorem continuousOn_of_inclusion_analytic {f : ℂ → Space} {U : Set ℂ}
    (hU : IsOpen U) {C : ℝ} (hC : 0 ≤ C)
    (hf : AnalyticOnNhd ℂ (fun z => inclusion (f z)) U)
    (hbound : ∀ z ∈ U, ‖f z‖ ≤ C) : ContinuousOn f U := by
  intro z hz
  obtain ⟨R, hR, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hz)
  let K : NNReal := ⟨2 * C / R, by positivity⟩
  have ha : AnalyticOnNhd ℂ (fun w => inclusion (f (z+w))) (closedBall 0 R) := by
    intro w hw
    have hzw : z+w ∈ closedBall z R := by simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero] using hw
    exact AnalyticAt.comp (f := fun w : ℂ => z+w) (hf (z+w) (hsub hzw))
      (analyticAt_const.add analyticAt_id)
  have hb : ∀ w ∈ closedBall (0 : ℂ) R,
      Summable (fun ν => ‖inclusion (f (z+w)) ν‖) ∧ ∑' ν, ‖inclusion (f (z+w)) ν‖ ≤ C := by
    intro w hw
    refine ⟨summable_norm _, ?_⟩
    rw [show (∑' ν, ‖inclusion (f (z+w)) ν‖) = ‖f (z+w)‖ from (norm_eq_tsum _).symm]
    apply hbound _ (hsub _)
    simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero] using hw
  have hLip : LipschitzOnWith K f (closedBall z (R/2)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro c hc d hd
    have he := analytic_curve_l1_sub_le hR hC ha hb (c := c-z) (d := d-z)
      (by simpa only [mem_closedBall, dist_eq_norm, sub_zero] using hc)
      (by simpa only [mem_closedBall, dist_eq_norm, sub_zero] using hd)
    rw [dist_eq_norm, dist_eq_norm]
    change ‖f c - f d‖ ≤ (2*C/R) * ‖c-d‖
    rw [norm_eq_tsum]
    simpa only [add_sub_cancel, inclusion_apply, lp.coeFn_sub, Pi.sub_apply,
      sub_sub_sub_cancel_right] using he.2
  exact (hLip.continuousOn.continuousAt (Metric.closedBall_mem_nhds z (by positivity))).continuousWithinAt

section Morera

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

theorem wedgeIntegral_clm (L : E →L[ℂ] F) (f : ℂ → E) (z w : ℂ)
    (hf : ContinuousOn f (Rectangle z w)) :
    wedgeIntegral z w (fun v => L (f v)) = L (wedgeIntegral z w f) := by
  have hh : IntervalIntegrable (fun x : ℝ => f (x + z.im * Complex.I)) volume z.re w.re := by
    apply ContinuousOn.intervalIntegrable
    apply hf.comp (by fun_prop : ContinuousOn (fun x : ℝ => (x : ℂ) + z.im * Complex.I) (uIcc z.re w.re))
    intro x hx
    simpa only [Rectangle, mem_reProdIm, add_re, ofReal_re, mul_re, ofReal_im,
      I_re, I_im, mul_zero, zero_mul, sub_self, add_zero, add_im, ofReal_im, zero_add,
      mul_im, mul_one] using And.intro hx (left_mem_uIcc : z.im ∈ uIcc z.im w.im)
  have hv : IntervalIntegrable (fun y : ℝ => f (w.re + y * Complex.I)) volume z.im w.im := by
    apply ContinuousOn.intervalIntegrable
    apply hf.comp (by fun_prop : ContinuousOn (fun y : ℝ => (w.re : ℂ) + y * Complex.I) (uIcc z.im w.im))
    intro y hy
    simpa only [Rectangle, mem_reProdIm, add_re, ofReal_re, mul_re, ofReal_im,
      I_re, I_im, mul_zero, zero_mul, sub_self, add_zero, add_im, zero_add,
      mul_im, mul_one] using And.intro (right_mem_uIcc : w.re ∈ uIcc z.re w.re) hy
  rw [wedgeIntegral, wedgeIntegral, L.intervalIntegral_comp_comm hh,
    L.intervalIntegral_comp_comm hv, map_add, map_smul]

theorem analyticOnNhd_of_injective_clm {f : ℂ → E} {U : Set ℂ} (hU : IsOpen U)
    (L : E →L[ℂ] F) (hL : Function.Injective L) (hc : ContinuousOn f U)
    (ha : AnalyticOnNhd ℂ (fun z => L (f z)) U) : AnalyticOnNhd ℂ f U := by
  have hd : DifferentiableOn ℂ (fun z => L (f z)) U := ha.differentiableOn
  have hcons : IsConservativeOn f U := by
    intro z w hrect
    apply hL
    rw [map_neg, ← wedgeIntegral_clm L f z w (hc.mono hrect)]
    have hrect' : Rectangle w z ⊆ U := by simpa only [Rectangle, uIcc_comm] using hrect
    rw [← wedgeIntegral_clm L f w z (hc.mono hrect')]
    exact hd.isConservativeOn z w hrect
  have hg := (isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU).mp ⟨hcons,hc⟩
  exact hg.analyticOnNhd hU

end Morera

theorem analyticOnNhd_of_inclusion {f : ℂ → Space} {U : Set ℂ}
    (hU : IsOpen U) {C : ℝ} (hC : 0 ≤ C)
    (hf : AnalyticOnNhd ℂ (fun z => inclusion (f z)) U)
    (hbound : ∀ z ∈ U, ‖f z‖ ≤ C) : AnalyticOnNhd ℂ f U :=
  analyticOnNhd_of_injective_clm hU inclusion inclusion_injective
    (continuousOn_of_inclusion_analytic hU hC hf hbound) hf

#print axioms analyticOnNhd_of_inclusion

end Maxwell.Continuum.FiberL1
