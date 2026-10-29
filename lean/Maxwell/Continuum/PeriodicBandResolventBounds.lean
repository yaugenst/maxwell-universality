import Maxwell.Continuum.PeriodicBandSeparation
import Maxwell.Continuum.RankOneBandInverseBounds

/-! Quantitative norm bound for the literal full-fiber resolvent, measured
by distance to the constructed band. The finite inverse is the actual
rank-one Schur formula, transported through the infinite fiber Feshbach
inverse on its maximal domain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber ClusterComplement FiberAnalytic PeriodicPerturbation CornerBridge Metric Set

theorem finiteSchurInverse_norm_le {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : e ∈ energyDisk) (hne : e ≠ scaledBand t) :
    ‖Ring.inverse (finiteSchurExtension (t, e))‖ ≤ 3 / ‖e - scaledBand t‖ + 40 := by
  have he' : ‖e - (Corner.lambdaStar : ℂ)‖ ≤ 1 / 100 := by
    simpa only [energyDisk, mem_closedBall, dist_eq_norm] using he
  have hV := perturbation_norm_le (t, e) (chart_energy_inBox ht he)
  have hg := actualCornerData.scalarResidual_ne_zero perturbationData t ht e he hne
  have hr := actualCornerData.resolvent_eq_ringInverse (perturbation (t, e)) e hV he' hg
  rw [finiteSchurExtension_expansion]
  change ‖Ring.inverse (RankOneBand.operator finiteK (perturbation (t, e)) e)‖ ≤ _
  rw [← hr]
  exact actualCornerData.resolvent_norm_le_bandRoot perturbationData t ht e he hne

theorem fullResolventExtension_norm_le_band {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : e ∈ energyDisk) (hne : e ≠ scaledBand t) :
    ‖fullResolventExtension (t, e)‖ ≤
      2 + 4 * backgroundAmplitude⁻¹ * (3 / ‖e - scaledBand t‖ + 40) := by
  have hmul := mul_le_mul_of_nonneg_left (finiteSchurInverse_norm_le ht he hne)
    (mul_nonneg (show (0 : ℝ) ≤ 4 by norm_num)
      (inv_nonneg.mpr backgroundAmplitude_pos.le))
  exact (fullResolventExtension_norm_le (t, e) (chart_energy_inBox ht he)).trans
    (add_le_add le_rfl hmul)

theorem actual_inverse_norm_le_band {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : e ∈ energyDisk) (hne : e ≠ scaledBand t)
    (R : SelfAdjointResolvent.BoundedInverse
      (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude)) :
    ‖R.map‖ ≤ 2 + 4 * backgroundAmplitude⁻¹ * (3 / ‖e - scaledBand t‖ + 40) := by
  have he' : ‖e - (Corner.lambdaStar : ℂ)‖ ≤ 1 / 50 := by
    have hn : ‖e - (Corner.lambdaStar : ℂ)‖ ≤ 1 / 100 := by
      simpa only [energyDisk, mem_closedBall, dist_eq_norm] using he
    linarith
  rw [R.unique_map (inverseAwayFromBand ht he' hne),
    ← fullResolventExtension_eq_inverseAwayFromBand ht he' hne]
  exact fullResolventExtension_norm_le_band ht he hne

end Maxwell.Continuum.PeriodicBand
