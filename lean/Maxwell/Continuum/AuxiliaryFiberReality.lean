import Maxwell.Continuum.AuxiliaryFiberRegularity
import Maxwell.Continuum.CellBandFourierReversal
import Maxwell.Continuum.FiberNormalizationConjugation

/-! Exact conjugation and alias-reversal identities for the whole
continuum fiber inverse. These act on every alias and every polarization. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.Auxiliary

open FreeFiber PeriodicBand FiberAnalytic FiberNormalization CellBandFourier

attribute [local irreducible] fiberInverse fiberResolvent fullResolventExtension scaledBand
  PeriodicPerturbation.perturbation PeriodicPerturbation.finiteK CornerBridge.topState
  RankOneBand.Data.bandRoot

theorem boundedInverse_map_of_graph {A : FiberSpace →ₗ.[ℂ] FiberSpace}
    (R : SelfAdjointResolvent.BoundedInverse A) {u v : FiberSpace}
    (h : (u, v) ∈ A.graph) : R.map v = u := by
  obtain ⟨w, hw, hv⟩ := (LinearPMap.mem_graph_iff A).mp h
  exact (congrArg R.map hv.symm).trans ((R.map_apply w).trans hw)

theorem fiberResolvent_star {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) (f : FiberSpace) :
    fiberResolvent z σ q (star f) = star (fiberResolvent z σ q f) := by
  have hg := material_graph_star (realMomentum q) (sampledEnergy z σ) backgroundAmplitude
    _ _ (fiberResolvent_graph D hσ0 hσ q hq f)
  rw [star_realMomentum] at hg
  have hE : star (sampledEnergy z σ) = sampledEnergy z σ := by
    simp only [sampledEnergy, Complex.star_def, Complex.conj_ofReal]
  rw [hE] at hg
  have hi := boundedInverse_map_of_graph (fiberInverse D hσ0 hσ q hq) hg
  rwa [← fiberResolvent_eq_inverse D hσ0 hσ q hq] at hi

theorem realMomentum_neg (q : Corner.Vec) : realMomentum (-q) = -realMomentum q := by
  funext j
  simp only [realMomentum, Pi.neg_apply, Complex.ofReal_neg]

theorem fiberResolvent_reverse {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) (f : FiberSpace) :
    fiberResolvent z σ (-q) (reversal f) = reversal (fiberResolvent z σ q f) := by
  have hqn : ‖realMomentum (-q)‖ ≤ 4 * smallRadius := by
    rwa [realMomentum_neg, norm_neg]
  have hg := material_graph_reverse (realMomentum q) (sampledEnergy z σ) backgroundAmplitude
    _ _ (fiberResolvent_graph D hσ0 hσ q hq f)
  rw [← realMomentum_neg] at hg
  have hi := boundedInverse_map_of_graph (fiberInverse D hσ0 hσ (-q) hqn) hg
  rwa [← fiberResolvent_eq_inverse D hσ0 hσ (-q) hqn] at hi

theorem fiberResolvent_reverse_star {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) (f : FiberSpace) :
    fiberResolvent z σ (-q) (reversal (star f)) =
      reversal (star (fiberResolvent z σ q f)) := by
  rw [fiberResolvent_reverse D hσ0 hσ q hq, fiberResolvent_star D hσ0 hσ q hq]

end Maxwell.Continuum.Auxiliary
