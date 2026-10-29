import Maxwell.Continuum.FiberNormalizationNormalized
import Maxwell.Continuum.BandWavePacketReality

/-! Actual zero-momentum perturbation estimates relative to the certified
selected corner state, before the absolute Fourier comparison. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.CellBandFourier

open FreeFiber ClusterComplement FiberAnalytic PeriodicPerturbation CornerBridge
  PeriodicBand FiberNormalization

attribute [local irreducible] perturbation finiteK topState RankOneBand.Data.bandRoot
  scaledBand clusterVector fiberVector normalizedFiberVector

set_option backward.isDefEq.respectTransparency false in
theorem clusterVector_zero_sub_top_bound :
    ‖clusterVector 0 - topState‖ ≤ 10240 * backgroundAmplitude := by
  have hb := chart_energy_inBox chart_zero (scaledBand_mem chart_zero)
  have hV := perturbation_sub_velocity_norm_le (0, scaledBand 0) hb
  rw [finiteVelocity_zero] at hV
  have hvzero : perturbation (0, scaledBand 0) - (0 : ClusterMap) =
      perturbation (0, scaledBand 0) := by
    apply ContinuousLinearMap.ext
    intro v
    change perturbation (0, scaledBand 0) v - (0 : clusterSpace) = _
    exact sub_zero _
  rw [hvzero] at hV
  have he : ‖scaledBand 0 - (Corner.lambdaStar : ℂ)‖ ≤ 1/100 := by
    simpa only [energyDisk, Metric.mem_closedBall, dist_eq_norm] using scaledBand_mem chart_zero
  have hc := actualCornerData.correctionVector_norm_le (perturbation (0, scaledBand 0))
    (scaledBand 0) (perturbation_norm_le _ hb) he
  have hcv : clusterVector 0 - topState = RankOneBand.correctionVector finiteK topState
      Corner.lambdaStar (perturbation (0, scaledBand 0)) (scaledBand 0) := by
    unfold clusterVector RankOneBand.Data.bandVector RankOneBand.eigenvectorLift
    rw [show actualCornerData.bandRoot perturbationData 0 = scaledBand 0 from by unfold scaledBand; rfl]
    change topState + RankOneBand.correctionVector finiteK topState Corner.lambdaStar
      (perturbation (0, scaledBand 0)) (scaledBand 0) - topState = _
    abel
  rw [hcv]
  linarith

theorem fiberVector_zero_sub_top_bound :
    ‖fiberVector 0 - topState.val‖ ≤ 10272 * backgroundAmplitude := by
  have h1 := fiberVector_complement_bound chart_zero
  have h2 := clusterVector_zero_sub_top_bound
  change ‖(clusterVector 0).val - topState.val‖ ≤ _ at h2
  have h := norm_add_le (fiberVector 0 - (clusterVector 0).val)
    ((clusterVector 0).val - topState.val)
  rw [sub_add_sub_cancel] at h
  linarith

theorem fiberVector_norm_lower {t : Momentum} (ht : t ∈ chart) : 1 ≤ ‖fiberVector t‖ := by
  have h := norm_inner_le_norm (𝕜 := ℂ) topState.val (fiberVector t)
  rw [fiberVector_gauge ht, norm_one,
    show ‖topState.val‖ = 1 from topState_norm, one_mul] at h
  exact h

theorem fiberVector_zero_real : star (fiberVector 0) = fiberVector 0 := by
  have hz : realMomentum (0 : Fin 3 → ℝ) = 0 := by funext j; simp [realMomentum]
  simpa only [hz] using fiberVector_real (0 : Fin 3 → ℝ) (hz.symm ▸ chart_zero)

theorem normalizedFiberVector_zero_eq :
    normalizedFiberVector 0 = (‖fiberVector 0‖ : ℂ)⁻¹ • fiberVector 0 := by
  unfold normalizedFiberVector
  exact BandWavePacket.normalize_real_formula _ fiberVector_zero_real

theorem inverse_norm_zero_le : ‖(‖fiberVector 0‖ : ℂ)⁻¹‖ ≤ 1 := by
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact inv_le_one_of_one_le₀ (fiberVector_norm_lower chart_zero)

theorem inverse_norm_zero_sub_one_bound :
    ‖(‖fiberVector 0‖ : ℂ)⁻¹ - 1‖ ≤ 10272 * backgroundAmplitude := by
  have hn := fiberVector_norm_lower chart_zero
  have hp : 0 < ‖fiberVector 0‖ := lt_of_lt_of_le (by norm_num) hn
  have hsmall : 0 ≤ 1 - ‖fiberVector 0‖⁻¹ := by
    linarith [inv_le_one_of_one_le₀ hn]
  have hdiff : 1 - ‖fiberVector 0‖⁻¹ ≤ ‖fiberVector 0‖ - 1 := by
    have hi := inv_mul_cancel₀ hp.ne'
    nlinarith [sq_nonneg (‖fiberVector 0‖ - 1)]
  have hnorm := norm_sub_norm_le (fiberVector 0) topState.val
  rw [show ‖topState.val‖ = 1 from topState_norm] at hnorm
  have heq : (‖fiberVector 0‖ : ℂ)⁻¹ - 1 = ((‖fiberVector 0‖⁻¹ - 1 : ℝ) : ℂ) := by
    norm_cast
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
  linarith [fiberVector_zero_sub_top_bound]

#print axioms clusterVector_zero_sub_top_bound
#print axioms inverse_norm_zero_sub_one_bound

end Maxwell.Continuum.CellBandFourier
