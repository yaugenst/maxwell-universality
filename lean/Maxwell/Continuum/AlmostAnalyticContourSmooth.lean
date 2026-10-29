import Maxwell.Continuum.AlmostAnalyticContourProduct

/-! Joint smoothness and compact spatial support of the contour
integrand, including points outside the analytic momentum chart. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.AlmostAnalytic

open Complex FreeFiber PeriodicBand Auxiliary Set Metric Filter
open scoped Topology

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem coefficient_contDiff (j : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (coefficient j) := by
  unfold coefficient
  exact ((contDiff_const.mul Complex.ofRealCLM.contDiff).pow j).div_const _

theorem cutoffTaylor_joint_contDiff (K : ℕ) (β : Space) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Space => cutoffTaylor K smallRadius p.2 β p.1) := by
  unfold cutoffTaylor
  apply ContDiff.sum
  intro j _
  exact ((coefficient_contDiff j).comp contDiff_fst).mul
    (Complex.ofRealCLM.contDiff.comp ((cutoffDerivative_contDiff j β).comp contDiff_snd))

theorem shiftedMomentum_joint_contDiff (β : Space) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Space => shiftedMomentum p.2 β p.1) := by
  unfold shiftedMomentum
  exact (realMomentumMap.contDiff.comp contDiff_snd).add
    ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_fst)).smul contDiff_const)

theorem contourProduct_zero_outside (K : ℕ) (β : Space) (Y : Momentum → F) (s : ℝ)
    {q : Space} (hq : 4*smallRadius < ‖q‖) : contourProduct K β Y s q = 0 := by
  have hz : cutoffTaylor K smallRadius q β s = 0 := image_eq_zero_of_notMem_tsupport
    (f := fun x : Space => cutoffTaylor K smallRadius x β s) (by
    intro hm
    have hb := cutoffTaylor_tsupport K β s hm
    have hn : ‖q‖ ≤ 4*smallRadius := by simpa only [mem_closedBall, dist_zero_right] using hb
    exact hq.not_ge hn)
  rw [contourProduct, hz, zero_smul]

variable [CompleteSpace F]

theorem contourProduct_joint_contDiffAt (K : ℕ) (β : Space) (Y : Momentum → F)
    (p : ℝ × Space)
    (hY : ‖p.2‖ ≤ 4*smallRadius → AnalyticAt ℂ Y (shiftedMomentum p.2 β p.1)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (Function.uncurry (contourProduct K β Y)) p := by
  by_cases hq : ‖p.2‖ ≤ 4*smallRadius
  · have hy : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun w : ℝ × Space => Y (shiftedMomentum w.2 β w.1)) p :=
      ((hY hq).contDiffAt.restrict_scalars ℝ).comp p (shiftedMomentum_joint_contDiff β).contDiffAt
    exact (cutoffTaylor_joint_contDiff K β).contDiffAt.smul hy
  · have hn : 4*smallRadius < ‖p.2‖ := lt_of_not_ge hq
    have hz : Function.uncurry (contourProduct K β Y) =ᶠ[𝓝 p] (fun _ => 0) := by
      have he : ∀ᶠ w : ℝ × Space in 𝓝 p, 4*smallRadius < ‖w.2‖ :=
        continuous_snd.norm.continuousAt.eventually (eventually_gt_nhds hn)
      filter_upwards [he] with w hw
      exact contourProduct_zero_outside K β Y w.1 hw
    exact contDiffAt_const.congr_of_eventuallyEq hz

theorem contourProduct_contDiff (K : ℕ) (β : Space) (Y : Momentum → F) (s : ℝ)
    (hY : ∀ q : Space, ‖q‖ ≤ 4*smallRadius → AnalyticAt ℂ Y (shiftedMomentum q β s)) :
    ContDiff ℝ (⊤ : ℕ∞) (contourProduct K β Y s) := by
  apply contDiff_iff_contDiffAt.mpr
  intro q
  exact (contourProduct_joint_contDiffAt K β Y (s,q) (hY q)).comp q
    (contDiffAt_const.prodMk contDiffAt_id)

omit [CompleteSpace F] in
theorem contourProduct_tsupport (K : ℕ) (β : Space) (Y : Momentum → F) (s : ℝ) :
    tsupport (contourProduct K β Y s) ⊆ closedBall (0 : Space) (4*smallRadius) := by
  apply closure_minimal _ isClosed_closedBall
  intro q hq
  by_contra hn
  have hn' : 4*smallRadius < ‖q‖ := by
    simpa only [mem_closedBall, dist_zero_right, not_le] using hn
  exact (Function.mem_support.mp hq) (contourProduct_zero_outside K β Y s hn')

omit [CompleteSpace F] in
theorem contourProduct_compact (K : ℕ) (β : Space) (Y : Momentum → F) (s : ℝ) :
    HasCompactSupport (contourProduct K β Y s) :=
  (isCompact_closedBall (0 : Space) (4*smallRadius)).of_isClosed_subset isClosed_closure
    (contourProduct_tsupport K β Y s)

end Maxwell.Continuum.AlmostAnalytic
