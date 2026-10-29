import Maxwell.Green.Implicit
import Maxwell.Green.CauchyRemainder
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! Uniform normal disks for the moving simple pole. -/

noncomputable section

open Filter Metric Set Complex
open scoped Topology

namespace Maxwell.Green

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- The derivative of a normal slice is the corresponding component of the
actual joint Fréchet derivative. -/
theorem deriv_normal_slice {F : W × ℂ → ℂ} {w : W} {u : ℂ}
    (hF : AnalyticAt ℂ F (w, u)) :
    deriv (fun z => F (w, z)) u = (fderiv ℂ F (w, u)) (0, 1) := by
  have h := hF.differentiableAt.hasFDerivAt.comp_hasDerivAt u
    ((hasDerivAt_const u w).prodMk (hasDerivAt_id u))
  exact h.deriv

/-- Joint analyticity, normal simplicity and the implicit uniqueness
neighborhood provide one fixed disk for every nearby transverse parameter.
The disk contains exactly the moving simple zero. -/
theorem exists_uniform_normal_disk
    (A F : W × ℂ → ℂ) (p : W → ℂ)
    (hA : AnalyticAt ℂ A (0, 0)) (hF : AnalyticAt ℂ F (0, 0))
    (hp : ContinuousAt p 0) (hp₀ : p 0 = 0)
    (hu : (fderiv ℂ F (0, 0)) (0, 1) ≠ 0)
    (huniq : ∀ᶠ z in 𝓝 ((0, 0) : W × ℂ), F z = 0 ↔ p z.1 = z.2) :
    ∃ r > 0, ∃ R > 0, ∀ w, ‖w‖ ≤ r →
      ‖p w‖ < R / 2 ∧
      (∀ u ∈ closedBall (0 : ℂ) R, AnalyticAt ℂ A (w, u) ∧ AnalyticAt ℂ F (w, u)) ∧
      AnalyticOnNhd ℂ (fun u => A (w, u)) (closedBall 0 R) ∧
      AnalyticOnNhd ℂ (fun u => F (w, u)) (closedBall 0 R) ∧
      F (w, p w) = 0 ∧ deriv (fun u => F (w, u)) (p w) ≠ 0 ∧
      (∀ u ∈ closedBall (0 : ℂ) R, F (w, u) = 0 → u = p w) := by
  have hn := eventually_normal_derivative_ne_zero F hF hu
  obtain ⟨δ, hδ, hlocal⟩ := Metric.eventually_nhds_iff.mp
    (hA.eventually_analyticAt.and (hF.eventually_analyticAt.and (hn.and huniq)))
  let R := δ / 4
  have hR : 0 < R := by dsimp [R]; positivity
  have hpsmall : ∀ᶠ w in 𝓝 (0 : W), ‖p w‖ < R / 2 := by
    have h := hp.tendsto.eventually (ball_mem_nhds (p 0) (by positivity : 0 < R / 2))
    simpa only [mem_ball, hp₀, dist_zero_right] using h
  obtain ⟨t, ht, hpt⟩ := Metric.eventually_nhds_iff.mp hpsmall
  let r := min (δ / 4) (t / 2)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrδ : r < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hrt : r < t := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  refine ⟨r, hr, R, hR, fun w hw => ?_⟩
  have hpw : ‖p w‖ < R / 2 := hpt (by simpa only [dist_zero_right] using hw.trans_lt hrt)
  have hwu (u : ℂ) (huR : ‖u‖ ≤ R) : dist (w, u) (0, 0) < δ := by
    rw [dist_eq_norm, Prod.mk_sub_mk, sub_zero, sub_zero, Prod.norm_def]
    exact max_lt (hw.trans_lt hrδ) (huR.trans_lt (by dsimp [R]; linarith))
  have hwp := hlocal (hwu (p w) (hpw.le.trans (by linarith)))
  refine ⟨hpw, ?_, ?_, ?_, hwp.2.2.2.mpr rfl, ?_, ?_⟩
  · intro u huR
    have hh := hlocal (hwu u (by simpa only [mem_closedBall, dist_zero_right] using huR))
    exact ⟨hh.1, hh.2.1⟩
  · intro u huR
    have hh := (hlocal (hwu u (by simpa only [mem_closedBall, dist_zero_right] using huR))).1
    exact hh.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  · intro u huR
    have hh := (hlocal (hwu u (by simpa only [mem_closedBall, dist_zero_right] using huR))).2.1
    exact hh.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  · rw [deriv_normal_slice hwp.2.1]
    exact hwp.2.2.1
  · intro u huR hzero
    exact ((hlocal (hwu u (by simpa only [mem_closedBall, dist_zero_right] using huR))).2.2.2.mp hzero).symm

/-- A nonzero analytic denominator on the fixed outer circle has one quotient
bound for every parameter in the compact transverse disk. This is the bound
used by the uniform normal-derivative estimates. -/
theorem exists_uniform_circle_quotient_bound [ProperSpace W]
    (A F : W × ℂ → ℂ) (r R : ℝ)
    (hA : ∀ w ∈ closedBall (0 : W) r, ∀ u ∈ sphere (0 : ℂ) R, AnalyticAt ℂ A (w, u))
    (hF : ∀ w ∈ closedBall (0 : W) r, ∀ u ∈ sphere (0 : ℂ) R, AnalyticAt ℂ F (w, u))
    (hn : ∀ w ∈ closedBall (0 : W) r, ∀ u ∈ sphere (0 : ℂ) R, F (w, u) ≠ 0) :
    ∃ M ≥ 0, ∀ w ∈ closedBall (0 : W) r, ∀ u ∈ sphere (0 : ℂ) R,
      ‖A (w, u) / F (w, u)‖ ≤ M := by
  let s := closedBall (0 : W) r ×ˢ sphere (0 : ℂ) R
  have hs : IsCompact s := (isCompact_closedBall (0 : W) r).prod (isCompact_sphere (0 : ℂ) R)
  have ha : ContinuousOn A s := fun z hz => (hA z.1 hz.1 z.2 hz.2).continuousAt.continuousWithinAt
  have hf : ContinuousOn F s := fun z hz => (hF z.1 hz.1 z.2 hz.2).continuousAt.continuousWithinAt
  have hq : ContinuousOn (fun z => A z / F z) s := ha.div hf (fun z hz => hn z.1 hz.1 z.2 hz.2)
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuousOn hq
  refine ⟨max M 0, le_max_right _ _, fun w hw u hu => ?_⟩
  exact (hM (w, u) ⟨hw, hu⟩).trans (le_max_left _ _)

omit [NormedAddCommGroup W] [NormedSpace ℂ W] in
/-- A pole in the strict half-radius disk cannot lie on the chosen outer
circle, so uniqueness excludes every boundary denominator zero. -/
theorem normal_disk_boundary_nonzero {F : W × ℂ → ℂ} {p : W → ℂ}
    {w : W} {R : ℝ} (hR : 0 < R) (hp : ‖p w‖ < R / 2)
    (huniq : ∀ u ∈ closedBall (0 : ℂ) R, F (w, u) = 0 → u = p w) :
    ∀ u ∈ sphere (0 : ℂ) R, F (w, u) ≠ 0 := by
  intro u hu hz
  have heq := huniq u (sphere_subset_closedBall hu) hz
  have hn : ‖u‖ = R := by simpa only [mem_sphere, dist_zero_right] using hu
  rw [heq] at hn
  linarith

end Maxwell.Green
