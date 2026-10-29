import Maxwell.Green.QuadraticControl
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! Relative anisotropic Taylor comparison from a positive Hessian.
The comparison uses the actual Hessian quadratic form, not an isotropic
replacement, so it supplies the whitening ellipsoid rate estimates. -/

noncomputable section

namespace Maxwell.Green

open Filter Metric Set
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

theorem exists_relative_quadratic_comparison
    (F : E → ℝ) (hF : ContDiffAt ℝ ∞ F 0) (hzero : F 0 = 0)
    (hstationary : fderiv ℝ F 0 = 0)
    (hpositive : ∀ x : E, x ≠ 0 → 0 < (fderiv ℝ (fderiv ℝ F) 0) x x)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ r > 0, ∀ x : E, ‖x‖ ≤ r →
      (1 - δ) * (fderiv ℝ (fderiv ℝ F) 0) x x / 2 ≤ F x ∧
      F x ≤ (1 + δ) * (fderiv ℝ (fderiv ℝ F) 0) x x / 2 := by
  let DF := fderiv ℝ F
  let H := fderiv ℝ DF
  obtain ⟨m, hm, hmlower⟩ := positive_bilinear_has_uniform_lower (H 0) hpositive
  have hDF : ContDiffAt ℝ ∞ DF 0 := hF.fderiv_right (m := ∞) (by simp)
  have hH : ContDiffAt ℝ ∞ H 0 := hDF.fderiv_right (m := ∞) (by simp)
  have hnearH : ∀ᶠ y in 𝓝 (0 : E), ‖H y - H 0‖ < δ * m := by
    have hc : ContinuousAt (fun y => H y - H 0) (0 : E) :=
      hH.continuousAt.sub continuousAt_const
    have hcn : ContinuousAt (fun y => ‖H y - H 0‖) (0 : E) :=
      @ContinuousAt.norm E (E →L[ℝ] E →L[ℝ] ℝ) _ _ _ _ hc
    exact hcn.eventually (gt_mem_nhds (by
      simpa only [sub_self, ContinuousLinearMap.opNorm_zero] using mul_pos hδ hm))
  have hnearD : ∀ᶠ y in 𝓝 (0 : E), HasFDerivAt F (DF y) y ∧ HasFDerivAt DF (H y) y := by
    have heF : ∀ᶠ y in 𝓝 (0 : E), ContDiffAt ℝ 1 F y :=
      (hF.of_le (by simp)).eventually (by simp)
    have heD : ∀ᶠ y in 𝓝 (0 : E), ContDiffAt ℝ 1 DF y :=
      (hDF.of_le (by simp)).eventually (by simp)
    filter_upwards [heF, heD] with y hy hy'
    exact ⟨hy.differentiableAt (by simp) |>.hasFDerivAt,
      hy'.differentiableAt (by simp) |>.hasFDerivAt⟩
  obtain ⟨s, hs, hnear⟩ := Metric.eventually_nhds_iff_ball.mp (hnearD.and hnearH)
  refine ⟨s / 2, by positivity, ?_⟩
  intro x hx
  have hline (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : t • x ∈ ball (0 : E) s := by
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    have hn : t * ‖x‖ ≤ ‖x‖ := mul_le_of_le_one_left (norm_nonneg _) ht.2
    exact (hn.trans hx).trans_lt (by linarith)
  have hfirst (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ => F (t • x)) (DF (t • x) x) t := by
    exact (hnear _ (hline t ht)).1.1.comp_hasDerivAt t
      (by simpa using (hasDerivAt_id t).smul_const x)
  have hsecond (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ => DF (t • x) x) (H (t • x) x x) t := by
    have hd := (hnear _ (hline t ht)).1.2.comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const x)
    simpa using hd.clm_apply (hasDerivAt_const t x)
  have hcompare (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      |H (t • x) x x - H 0 x x| ≤ δ * H 0 x x := by
    have he : |H (t • x) x x - H 0 x x| ≤ ‖H (t • x) - H 0‖ * ‖x‖ ^ 2 := by
      simpa only [sub_apply, Real.norm_eq_abs] using
        norm_bilinear_diagonal_le (H (t • x) - H 0) x
    calc
      _ ≤ ‖H (t • x) - H 0‖ * ‖x‖ ^ 2 := he
      _ ≤ (δ * m) * ‖x‖ ^ 2 := mul_le_mul_of_nonneg_right
        (hnear _ (hline t ht)).2.le (sq_nonneg _)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left (hmlower x) hδ.le]
  have hlo := quadratic_taylor_lower_unit
    (fun t : ℝ => F (t • x)) (fun t : ℝ => DF (t • x) x)
    (fun t : ℝ => H (t • x) x x) ((1 - δ) * H 0 x x / 2) hfirst hsecond
    (fun t ht => by have h := (abs_le.mp (hcompare t ht)).1; linarith)
  have hup := quadratic_taylor_lower_unit
    (fun t : ℝ => -F (t • x)) (fun t : ℝ => -DF (t • x) x)
    (fun t : ℝ => -H (t • x) x x) (-(1 + δ) * H 0 x x / 2)
    (fun t ht => (hfirst t ht).neg) (fun t ht => (hsecond t ht).neg)
    (fun t ht => by have h := (abs_le.mp (hcompare t ht)).2; linarith)
  have hDFzero : DF 0 = 0 := hstationary
  simp only [zero_smul, one_smul, hzero, hDFzero, zero_apply,
    zero_add, neg_zero] at hlo hup
  exact ⟨hlo, by linarith⟩

end Maxwell.Green
