import Maxwell.Continuum.AlmostAnalyticSupport
import Maxwell.Continuum.WellFourierDeriv
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! The boundary-free spatial integration by parts used in the
almost-analytic contour movement. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.AlmostAnalytic

open MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem integral_directional_eq_zero (g : Space → F)
    (hg : ContDiff ℝ 1 g) (hs : HasCompactSupport g) (v : Space) :
    (∫ q, fderiv ℝ g q v) = 0 := by
  have hd : Continuous (fun q => fderiv ℝ g q v) :=
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hs' : HasCompactSupport (fun q => fderiv ℝ g q v) := by
    exact (hs.fderiv ℝ).comp_left (g := fun A : Space →L[ℝ] F => A v) rfl
  have hint := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    (f := fun _ : Space => (1 : ℝ)) (g := g) (v := v) (μ := volume)
    (by simpa only [fderiv_const_apply, zero_apply, zero_smul] using
      (integrable_zero Space F volume : Integrable (fun _ : Space => (0 : F))))
    (by simpa only [one_smul] using hd.integrable_of_hasCompactSupport hs')
    (by simpa only [one_smul] using hg.continuous.integrable_of_hasCompactSupport hs)
    (fun _ _ => differentiableAt_const _) (fun q _ => hg.differentiable (by norm_num) q)
  simpa only [one_smul, fderiv_const_apply, zero_apply, zero_smul,
    integral_zero, neg_zero] using hint

theorem integral_norm_compact_le (g : Space → F) {C : ℝ} (hC : 0 ≤ C)
    (hs : Function.support g ⊆ Metric.closedBall (0 : Space) 1)
    (hb : ∀ q, ‖g q‖ ≤ C) : ‖∫ q, g q‖ ≤ 8*C := by
  have hi : Integrable ((Metric.closedBall (0 : Space) 1).indicator (fun _ : Space => C)) volume :=
    (integrableOn_const (isCompact_closedBall (0 : Space) 1).measure_lt_top.ne).integrable_indicator
      Metric.isClosed_closedBall.measurableSet
  have hbound : ∀ q, ‖g q‖ ≤ (Metric.closedBall (0 : Space) 1).indicator (fun _ : Space => C) q := by
    intro q
    by_cases hq : q ∈ Metric.closedBall (0 : Space) 1
    · rw [Set.indicator_of_mem hq]
      exact hb q
    · rw [Set.indicator_of_notMem hq, Function.notMem_support.mp (fun hm => hq (hs hm)), norm_zero]
  calc
    _ ≤ ∫ q, ‖g q‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ q, (Metric.closedBall (0 : Space) 1).indicator (fun _ : Space => C) q :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hi
        (Filter.Eventually.of_forall hbound)
    _ = (volume : Measure Space).real (Metric.closedBall 0 1) * C := by
      rw [integral_indicator_const C Metric.isClosed_closedBall.measurableSet, smul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right Well.unitBall_volume_le_eight hC

end Maxwell.Continuum.AlmostAnalytic
