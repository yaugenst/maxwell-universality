import Maxwell.Continuum.AuxiliaryFiberInverse

/-! Continuity and the exact source equation for the actual fiber inverse. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.Auxiliary

open FreeFiber PeriodicBand FiberAnalytic

attribute [local irreducible] fiberInverse fullResolventExtension scaledBand
  PeriodicPerturbation.perturbation PeriodicPerturbation.finiteK CornerBridge.topState
  RankOneBand.Data.bandRoot

theorem fiberParameter_continuous : Continuous fiberParameter := by
  unfold fiberParameter unscale realMomentum
  apply continuous_pi
  intro j
  exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply j))

theorem fiberResolvent_continuousAt {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) :
    ContinuousAt (fiberResolvent z σ) q := by
  have hR := (fullResolventExtension_analytic_wide (fiberParameter_chart q hq)
    (sampledScaledEnergy_wide D hσ0 hσ q hq)
    (sampledScaledEnergy_ne_band D hσ0 hσ q hq)).continuousAt
  have hp : ContinuousAt (fun p : Corner.Vec => (fiberParameter p, sampledScaledEnergy z σ)) q :=
    fiberParameter_continuous.continuousAt.prodMk continuousAt_const
  unfold fiberResolvent
  exact ContinuousAt.comp (f := fun p : Corner.Vec => (fiberParameter p, sampledScaledEnergy z σ)) hR hp

theorem boundedInverse_graph {A : FiberSpace →ₗ.[ℂ] FiberSpace}
    (R : SelfAdjointResolvent.BoundedInverse A) (f : FiberSpace) : (R.map f, f) ∈ A.graph := by
  rw [LinearPMap.mem_graph_iff]
  exact ⟨⟨R.map f, R.mem_domain f⟩, rfl, R.apply_map f⟩

theorem fiberResolvent_graph {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) (f : FiberSpace) :
    (fiberResolvent z σ q f, f) ∈
      (materialFiber (realMomentum q) (sampledEnergy z σ) backgroundAmplitude).graph := by
  have hg := boundedInverse_graph (fiberInverse D hσ0 hσ q hq) f
  rw [← fiberResolvent_eq_inverse D hσ0 hσ q hq] at hg
  exact hg

end Maxwell.Continuum.Auxiliary
