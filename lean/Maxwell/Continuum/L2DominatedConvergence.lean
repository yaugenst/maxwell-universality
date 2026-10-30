import Maxwell.Continuum.WeakCurl
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Dominated convergence for explicit representatives of complex L²
classes, along any countably generated parameter filter. -/

noncomputable section

namespace Maxwell.Continuum.L2Convergence

open MeasureTheory Filter
open scoped Topology

theorem norm_sq_integral {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (u : Lp ℂ 2 μ) : ‖u‖^2 = ∫ x, ‖u x‖^2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner u u)]
  simp only [inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow]

theorem tendsto_of_dominated {X I : Type*} [MeasurableSpace X]
    (μ : Measure X) {l : Filter I} [l.IsCountablyGenerated]
    (u : I → Lp ℂ 2 μ) (v : Lp ℂ 2 μ) (F : I → X → ℂ) (G : X → ℂ) (B : X → ℝ)
    (hu : ∀ t, u t =ᵐ[μ] F t) (hv : v =ᵐ[μ] G)
    (hF : ∀ᶠ t in l, AEStronglyMeasurable (F t) μ)
    (hG : AEStronglyMeasurable G μ)
    (hB : Integrable (fun x => B x^2) μ)
    (hFb : ∀ᶠ t in l, ∀ᵐ x ∂μ, ‖F t x‖ ≤ B x)
    (hGb : ∀ᵐ x ∂μ, ‖G x‖ ≤ B x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun t => F t x) l (𝓝 (G x))) :
    Tendsto u l (𝓝 v) := by
  have hm : ∀ᶠ t in l, AEStronglyMeasurable (fun x => ‖F t x-G x‖^2) μ :=
    hF.mono fun _ ht => (ht.sub hG).norm.pow 2
  have hb : ∀ᶠ t in l, ∀ᵐ x ∂μ, ‖‖F t x-G x‖^2‖ ≤ 4*B x^2 := by
    filter_upwards [hFb] with t ht
    filter_upwards [ht, hGb] with x hx hg
    have hn : ‖F t x-G x‖ ≤ 2*B x := (norm_sub_le _ _).trans (by linarith)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg (F t x-G x), norm_nonneg (G x)]
  have hp : ∀ᵐ x ∂μ, Tendsto (fun t => ‖F t x-G x‖^2) l (𝓝 (0 : ℝ)) := by
    filter_upwards [hlim] with x hx
    simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
      (hx.sub_const (G x)).norm.pow 2
  have hi := tendsto_integral_filter_of_dominated_convergence (fun x => 4*B x^2)
    hm hb (hB.const_mul 4) hp
  simp only [integral_zero] at hi
  have he (t : I) : ‖u t-v‖^2 = ∫ x, ‖F t x-G x‖^2 ∂μ := by
    rw [norm_sq_integral μ]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (u t) v, hu t, hv] with x hs hf hg
    rw [hs]
    simp only [Pi.sub_apply, hf, hg]
  have hs : Tendsto (fun t => ‖u t-v‖^2) l (𝓝 (0 : ℝ)) :=
    hi.congr fun t => (he t).symm
  have hn := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hs
  simp only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] at hn
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

#print axioms tendsto_of_dominated

end Maxwell.Continuum.L2Convergence
