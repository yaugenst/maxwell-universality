import Maxwell.Continuum.AlmostAnalyticContourSmooth

/-! The actual time derivative of the shifted cutoff-symbol product,
with the continuity and compact support required for integration. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.AlmostAnalytic

open Complex FreeFiber PeriodicBand Auxiliary Set Metric Filter
open scoped Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

def contourTimeDerivative (K : ℕ) (β : Space) (Y : Momentum → F) (s : ℝ) (q : Space) : F :=
  fderiv ℝ (Function.uncurry (contourProduct K β Y)) (s,q) (1,0)

theorem contourTimeDerivative_hasDerivAt (K : ℕ) (β : Space) (Y : Momentum → F)
    (s : ℝ) (q : Space)
    (hY : ‖q‖ ≤ 4*smallRadius → AnalyticAt ℂ Y (shiftedMomentum q β s)) :
    HasDerivAt (fun t => contourProduct K β Y t q) (contourTimeDerivative K β Y s q) s := by
  have hg := (contourProduct_joint_contDiffAt K β Y (s,q) hY).differentiableAt (by simp)
  have hp : HasDerivAt (fun t : ℝ => (t,q)) (1,0) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s q)
  exact hg.hasFDerivAt.comp_hasDerivAt s hp

theorem contourTimeDerivative_continuousAt (K : ℕ) (β : Space) (Y : Momentum → F)
    (p : ℝ × Space)
    (hY : ‖p.2‖ ≤ 4*smallRadius → AnalyticAt ℂ Y (shiftedMomentum p.2 β p.1)) :
    ContinuousAt (Function.uncurry (contourTimeDerivative K β Y)) p :=
  ((contourProduct_joint_contDiffAt K β Y p hY).continuousAt_fderiv (by simp)).clm_apply
    continuousAt_const

theorem contourTimeDerivative_continuous (K : ℕ) (β : Space) (Y : Momentum → F) (s : ℝ)
    (hY : ∀ q, ‖q‖ ≤ 4*smallRadius → AnalyticAt ℂ Y (shiftedMomentum q β s)) :
    Continuous (contourTimeDerivative K β Y s) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  exact (contourTimeDerivative_continuousAt K β Y (s,q) (hY q)).comp
    (continuousAt_const.prodMk continuousAt_id)

omit [CompleteSpace F] in
theorem contourTimeDerivative_zero_outside (K : ℕ) (β : Space) (Y : Momentum → F) (s : ℝ)
    {q : Space} (hq : 4*smallRadius < ‖q‖) : contourTimeDerivative K β Y s q = 0 := by
  have hz : Function.uncurry (contourProduct K β Y) =ᶠ[𝓝 (s,q)] (fun _ => 0) := by
    have he : ∀ᶠ w : ℝ × Space in 𝓝 (s,q), 4*smallRadius < ‖w.2‖ :=
      continuous_snd.norm.continuousAt.eventually (eventually_gt_nhds hq)
    filter_upwards [he] with w hw
    exact contourProduct_zero_outside K β Y w.1 hw
  rw [contourTimeDerivative, hz.fderiv_eq, fderiv_const_apply, zero_apply]

omit [CompleteSpace F] in
theorem contourTimeDerivative_tsupport (K : ℕ) (β : Space) (Y : Momentum → F) (s : ℝ) :
    tsupport (contourTimeDerivative K β Y s) ⊆ closedBall (0 : Space) (4*smallRadius) := by
  apply closure_minimal _ isClosed_closedBall
  intro q hq
  by_contra hn
  have hn' : 4*smallRadius < ‖q‖ := by simpa only [mem_closedBall, dist_zero_right, not_le] using hn
  exact (Function.mem_support.mp hq) (contourTimeDerivative_zero_outside K β Y s hn')

omit [CompleteSpace F] in
theorem contourTimeDerivative_compact (K : ℕ) (β : Space) (Y : Momentum → F) (s : ℝ) :
    HasCompactSupport (contourTimeDerivative K β Y s) :=
  (isCompact_closedBall (0 : Space) (4*smallRadius)).of_isClosed_subset isClosed_closure
    (contourTimeDerivative_tsupport K β Y s)

theorem contourProduct_defect_global (K : ℕ) (β : Space) (Y : Momentum → F) (s : ℝ) (q : Space)
    (hY : ‖q‖ ≤ 4*smallRadius → AnalyticAt ℂ Y (shiftedMomentum q β s)) :
    contourTimeDerivative K β Y s q =
      I • fderiv ℝ (contourProduct K β Y s) q β +
        cutoffDefect K β s q • Y (shiftedMomentum q β s) := by
  by_cases hq : ‖q‖ ≤ 4*smallRadius
  · have he := contourProduct_defect K β Y s q (hY hq).differentiableAt
    rw [(contourTimeDerivative_hasDerivAt K β Y s q hY).deriv] at he
    exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)
  · have hn : 4*smallRadius < ‖q‖ := lt_of_not_ge hq
    have hg : contourProduct K β Y s =ᶠ[𝓝 q] (fun _ => 0) := by
      have he : ∀ᶠ p : Space in 𝓝 q, 4*smallRadius < ‖p‖ :=
        continuous_norm.continuousAt.eventually (eventually_gt_nhds hn)
      filter_upwards [he] with p hp
      exact contourProduct_zero_outside K β Y s hp
    have hd : cutoffDefect K β s q = 0 := image_eq_zero_of_notMem_tsupport (by
      intro hm
      exact hq (cutoffDefect_tsupport K β s hm).2)
    rw [contourTimeDerivative_zero_outside K β Y s hn, hg.fderiv_eq,
      fderiv_const_apply, zero_apply, hd, smul_zero, zero_smul, zero_add]

end Maxwell.Continuum.AlmostAnalytic
