import Maxwell.Continuum.PeriodicBand
import Maxwell.Continuum.RankOneBandComparison

/-! Comparison with the affine corner band. The displacement is obtained
from the literal infinite-alias self-energy, with explicit constants. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber ClusterComplement FiberAnalytic PeriodicPerturbation CornerBridge Metric Set

attribute [local irreducible] perturbation finiteK topState RankOneBand.Data.bandRoot

theorem cornerPerturbationData : RankOneBand.PerturbationData
    (fun t _ => finiteVelocity t) chart Corner.lambdaStar where
  small t ht _ _ := (finiteVelocity_norm_le t (chart_closed_bounds ht)).trans (by norm_num)
  energy_lipschitz _ _ := by
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro e _ d _
    simp only [sub_self, norm_zero]
    positivity

def cornerBand (t : Momentum) : ℂ := actualCornerData.bandRoot cornerPerturbationData t

theorem cornerBand_mem {t : Momentum} (ht : t ∈ chart) : cornerBand t ∈ energyDisk :=
  actualCornerData.bandRoot_mem cornerPerturbationData t ht

theorem cornerBand_analytic : AnalyticOnNhd ℂ cornerBand chart := by
  apply actualCornerData.analyticOnNhd_bandRoot cornerPerturbationData ?_ chart_isOpen
  intro z _
  exact AnalyticAt.comp (f := fun w : Parameter => clusterVelocity w.1)
    (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := FiberMap) (F := ClusterMap)
      compressionCLM (clusterVelocity z.1)) (analyticAt_clusterVelocity z)

theorem finiteVelocity_zero : finiteVelocity (0 : Momentum) = 0 := by
  have hv : clusterVelocity (0 : Momentum) = 0 := by
    apply ContinuousLinearMap.ext
    intro u
    apply Subtype.ext
    funext ν
    change velocityBlock 0 ν (u ν) = 0
    rw [velocityBlock_apply]
    simp [bilinearDot]
  change compressionCLM (clusterVelocity 0) = 0
  rw [hv, map_zero]

theorem cornerBand_zero : cornerBand 0 = (Corner.lambdaStar : ℂ) := by
  have hdisk : (Corner.lambdaStar : ℂ) ∈ energyDisk := by
    simp only [energyDisk, mem_closedBall, dist_self]
    norm_num
  have he : RankOneBand.operator finiteK (finiteVelocity 0) (Corner.lambdaStar : ℂ) topState = 0 := by
    rw [finiteVelocity_zero]
    change finiteK topState + 0 - (Corner.lambdaStar : ℂ) • topState = 0
    rw [finiteK_topState, add_zero, sub_self]
  have hu : topState ≠ 0 := by
    intro h
    have hn := topState_norm
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  exact ((actualCornerData.kernel_nonzero_iff_bandRoot cornerPerturbationData 0 chart_zero
    (Corner.lambdaStar : ℂ) hdisk).mp ⟨topState, hu, he⟩).symm

theorem scaledBand_sub_cornerBand {t : Momentum} (ht : t ∈ chart) :
    ‖scaledBand t - cornerBand t‖ ≤ 1024 * backgroundAmplitude := by
  have h := actualCornerData.bandRoot_sub_bound perturbationData cornerPerturbationData t ht
    (ε := 256 * backgroundAmplitude) (mul_nonneg (by norm_num) backgroundAmplitude_pos.le)
    (fun e he => perturbation_sub_velocity_norm_le (t, e) (chart_energy_inBox ht he))
  change ‖scaledBand t - cornerBand t‖ ≤ _ at h
  exact h.trans_eq (by ring)

theorem scaledBand_zero_bound :
    ‖scaledBand 0 - (Corner.lambdaStar : ℂ)‖ ≤ 1024 * backgroundAmplitude := by
  rw [← cornerBand_zero]
  exact scaledBand_sub_cornerBand chart_zero

theorem clusterVector_norm_le {t : Momentum} (ht : t ∈ chart) : ‖clusterVector t‖ ≤ 2 :=
  actualCornerData.bandVector_norm_le perturbationData t ht

theorem clusterVector_sub_top_bound {t : Momentum} (ht : t ∈ chart) :
    ‖clusterVector t - topState‖ ≤ 5 / 32 :=
  actualCornerData.bandVector_sub_unit_bound perturbationData t ht

end Maxwell.Continuum.PeriodicBand
