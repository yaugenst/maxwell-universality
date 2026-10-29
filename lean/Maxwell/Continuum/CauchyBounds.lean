import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Quantitative Cauchy estimates used for the actual periodic Schur correction
and the analytic band. The estimates apply to Banach-valued functions, so the
operator-valued correction requires no entrywise or dimension-dependent bound. -/

noncomputable section

namespace Maxwell.Continuum.CauchyBounds

open Set Metric
open scoped Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem closedBall_subset_of_norm_add_le {c : ℂ} {r R : ℝ}
    (hc : ‖c‖ + r ≤ R) : closedBall c r ⊆ closedBall 0 R := by
  intro z hz
  rw [mem_closedBall, dist_zero_right]
  have hz' : ‖z - c‖ ≤ r := by simpa only [mem_closedBall, dist_eq_norm] using hz
  calc
    ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by simpa only [sub_add_cancel] using norm_add_le (z - c) c
    _ ≤ r + ‖c‖ := by linarith
    _ ≤ R := by linarith

theorem norm_deriv_le {f : ℂ → F} {R C r : ℝ} {c : ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hC : ∀ z ∈ closedBall 0 R, ‖f z‖ ≤ C)
    (hr : 0 < r) (hc : ‖c‖ + r ≤ R) : ‖deriv f c‖ ≤ C / r := by
  have hsub := closedBall_subset_of_norm_add_le hc
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
    (hf.differentiableOn.diffContOnCl_ball hsub)
    (fun z hz => hC z (hsub (sphere_subset_closedBall hz)))

theorem norm_iteratedDeriv_le [CompleteSpace F] {f : ℂ → F} {R C r : ℝ} {c : ℂ}
    (n : ℕ) (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hC : ∀ z ∈ closedBall 0 R, ‖f z‖ ≤ C)
    (hr : 0 < r) (hc : ‖c‖ + r ≤ R) :
    ‖iteratedDeriv n f c‖ ≤ n.factorial * C / r ^ n := by
  have hsub := closedBall_subset_of_norm_add_le hc
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr
    (hf.differentiableOn.diffContOnCl_ball hsub)
    (fun z hz => hC z (hsub (sphere_subset_closedBall hz)))

/-- The full open disk suffices: approach its radius from below, rather than
assuming analytic continuation through the boundary. -/
theorem norm_iteratedDeriv_zero_le_of_open [CompleteSpace F] {f : ℂ → F} {R C : ℝ}
    (n : ℕ) (hf : AnalyticOnNhd ℂ f (ball 0 R))
    (hC : ∀ z ∈ ball 0 R, ‖f z‖ ≤ C) (hR : 0 < R) :
    ‖iteratedDeriv n f 0‖ ≤ n.factorial * C / R ^ n := by
  have hb : ∀ᶠ r : ℝ in 𝓝[<] R, ‖iteratedDeriv n f 0‖ ≤ n.factorial * C / r ^ n := by
    have hp : ∀ᶠ r : ℝ in 𝓝[<] R, 0 < r :=
      (eventually_gt_nhds hR).filter_mono nhdsWithin_le_nhds
    filter_upwards [hp, self_mem_nhdsWithin] with r hr hrR
    have hsub : closedBall (0 : ℂ) r ⊆ ball 0 R := closedBall_subset_ball hrR
    exact norm_iteratedDeriv_le n (hf.mono hsub) (fun z hz => hC z (hsub hz)) hr
      (by simp)
  have hl : Filter.Tendsto (fun r : ℝ => (n.factorial : ℝ) * C / r ^ n)
      (𝓝[<] R) (𝓝 ((n.factorial : ℝ) * C / R ^ n)) :=
    (continuousAt_const.div (continuousAt_id.pow n) (pow_ne_zero n hR.ne')).tendsto.mono_left
      nhdsWithin_le_nhds
  exact ge_of_tendsto hl hb

/-- The actual correction is bounded by 256 on the energy disk of radius 8.
Its energy derivative has the same bound throughout the smaller disk. -/
theorem correction_deriv_le {f : ℂ → F}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 8))
    (hC : ∀ z ∈ closedBall 0 8, ‖f z‖ ≤ 256)
    {c : ℂ} (hc : c ∈ closedBall 0 4) : ‖deriv f c‖ ≤ 256 := by
  have hc' : ‖c‖ ≤ 4 := by simpa only [mem_closedBall, dist_zero_right] using hc
  simpa only [div_one] using norm_deriv_le hf hC (r := 1) (by norm_num) (by linarith)

theorem correction_lipschitz {f : ℂ → F}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 8))
    (hC : ∀ z ∈ closedBall 0 8, ‖f z‖ ≤ 256) :
    LipschitzOnWith 256 f (closedBall 0 4) := by
  apply (convex_closedBall (0 : ℂ) (4 : ℝ)).lipschitzOnWith_of_nnnorm_deriv_le
  · intro z hz
    exact (hf z (closedBall_subset_closedBall (by norm_num) hz)).differentiableAt
  · intro z hz
    exact correction_deriv_le hf hC hz

theorem correction_sub_le {f : ℂ → F}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 8))
    (hC : ∀ z ∈ closedBall 0 8, ‖f z‖ ≤ 256)
    {c d : ℂ} (hc : c ∈ closedBall 0 4) (hd : d ∈ closedBall 0 4) :
    ‖f c - f d‖ ≤ 256 * ‖c - d‖ := by
  simpa only [dist_eq_norm, NNReal.coe_ofNat] using
    (correction_lipschitz hf hC).dist_le_mul c hc d hd

end Maxwell.Continuum.CauchyBounds
