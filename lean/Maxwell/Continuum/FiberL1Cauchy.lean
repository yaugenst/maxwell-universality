import Maxwell.Continuum.CauchyLipschitz
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! A dimension-free ℓ¹ Cauchy estimate for an actual analytic ℓ²-valued
curve. Finite norming functionals convert the uniform coefficient-sum
bound into a scalar holomorphic bound before passing to the full sum. -/

noncomputable section

namespace Maxwell.Continuum.FiberL1

open Set Metric

variable {ι H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem analytic_curve_sum_sub_le {f : ℂ → lp (fun _ : ι => H) 2} {R C : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hbound : ∀ z ∈ closedBall 0 R,
      Summable (fun i => ‖f z i‖) ∧ ∑' i, ‖f z i‖ ≤ C)
    {c d : ℂ} (hc : c ∈ closedBall 0 (R / 2)) (hd : d ∈ closedBall 0 (R / 2))
    (s : Finset ι) :
    (∑ i ∈ s, ‖f c i - f d i‖) ≤ (2 * C / R) * ‖c-d‖ := by
  classical
  choose g hg hgval using fun i : ι => exists_dual_vector'' ℂ (f c i - f d i)
  let L : lp (fun _ : ι => H) 2 →L[ℂ] ℂ :=
    ∑ i ∈ s, (g i).comp (lp.evalCLM ℂ (fun _ : ι => H) 2 i)
  have hL (v : lp (fun _ : ι => H) 2) : L v = ∑ i ∈ s, g i (v i) := by
    simp only [L, sum_apply, ContinuousLinearMap.comp_apply]
    rfl
  have hnorm (z : ℂ) (hz : z ∈ closedBall 0 R) : ‖L (f z)‖ ≤ C := by
    rw [hL]
    calc
      _ ≤ ∑ i ∈ s, ‖g i (f z i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ s, ‖f z i‖ := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [one_mul] using (g i).le_of_opNorm_le (hg i) (f z i)
      _ ≤ ∑' i, ‖f z i‖ := (hbound z hz).1.sum_le_tsum s (fun _ _ => norm_nonneg _)
      _ ≤ C := (hbound z hz).2
  have ha : AnalyticOnNhd ℂ (fun z => L (f z)) (closedBall 0 R) := by
    intro z hz
    exact AnalyticAt.comp (f := f) (L.analyticAt _) (hf z hz)
  have hb := CauchyBounds.bounded_curve_sub_le hR hC ha hnorm hc hd
  have hv : L (f c) - L (f d) = ((∑ i ∈ s, ‖f c i - f d i‖ : ℝ) : ℂ) := by
    rw [← map_sub, hL]
    simp only [lp.coeFn_sub, Pi.sub_apply, hgval, Complex.ofReal_sum]
    rfl
  rw [hv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)] at hb
  exact hb

theorem analytic_curve_l1_sub_le {f : ℂ → lp (fun _ : ι => H) 2} {R C : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hbound : ∀ z ∈ closedBall 0 R,
      Summable (fun i => ‖f z i‖) ∧ ∑' i, ‖f z i‖ ≤ C)
    {c d : ℂ} (hc : c ∈ closedBall 0 (R / 2)) (hd : d ∈ closedBall 0 (R / 2)) :
    Summable (fun i => ‖f c i - f d i‖) ∧
      (∑' i, ‖f c i - f d i‖) ≤ (2 * C / R) * ‖c-d‖ := by
  have hs := analytic_curve_sum_sub_le hR hC hf hbound hc hd
  exact ⟨summable_of_sum_le (fun _ => norm_nonneg _) hs,
    Real.tsum_le_of_sum_le (fun _ => norm_nonneg _) hs⟩

#print axioms analytic_curve_l1_sub_le

end Maxwell.Continuum.FiberL1
