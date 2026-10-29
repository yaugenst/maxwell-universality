import Maxwell.Continuum.PeriodicBandSeparatedBounds

/-! For real momentum the genuine spectral projection has norm at most
one. This yields the sharp pole coefficient needed by the continuum
auxiliary-resolvent conditioning estimate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber FiberAnalytic FiberNormalization Metric

theorem fullSpectralProjection_norm_le_real (t : Fin 3 → ℝ) (ht : realMomentum t ∈ chart) :
    ‖fullSpectralProjection (realMomentum t)‖ ≤ 1 := by
  rw [fullSpectralProjection_eq_bilinearProjection ht]
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  change ‖(bilinear (normalizedFiberVector (realMomentum t)) u) •
    normalizedFiberVector (realMomentum t)‖ ≤ _
  rw [norm_smul, normalizedFiberVector_norm_real t ht, mul_one, one_mul]
  simpa only [normalizedFiberVector_norm_real t ht, one_mul] using
    bilinear_norm_le (normalizedFiberVector (realMomentum t)) u

theorem fullResolventExtension_norm_le_real_band (t : Fin 3 → ℝ) (ht : realMomentum t ∈ chart)
    {e : ℂ} (he : e ∈ closedBall (scaledBand (realMomentum t)) (1 / 200))
    (hne : e ≠ scaledBand (realMomentum t)) :
    ‖fullResolventExtension (realMomentum t, e)‖ ≤
      ‖totalEnergy e - physicalBand (realMomentum t)‖⁻¹ + (2 : ℝ) ^ 112 := by
  have hC : ‖fullPoleResidue (realMomentum t)‖ ≤ 1 := by
    have h := fullSpectralProjection_norm_le_real t ht
    change ‖-fullPoleResidue (realMomentum t)‖ ≤ _ at h
    rwa [norm_neg] at h
  have hP : ‖((backgroundAmplitude : ℂ) * (e - scaledBand (realMomentum t)))⁻¹ •
      fullPoleResidue (realMomentum t)‖ ≤ ‖totalEnergy e - physicalBand (realMomentum t)‖⁻¹ := by
    change _ ≤ ‖totalEnergy e - totalEnergy (scaledBand (realMomentum t))‖⁻¹
    rw [totalEnergy_sub, norm_smul, norm_inv]
    exact (mul_le_mul_of_nonneg_left hC (inv_nonneg.mpr (norm_nonneg _))).trans_eq (mul_one _)
  rw [fullResolvent_pole_formula ht (centeredEnergyDisk_subset ht he) hne]
  exact (norm_add_le _ _).trans (add_le_add hP (fullSeparatedResolvent_norm_le ht he))

theorem actual_inverse_norm_le_real_band (t : Fin 3 → ℝ) (ht : realMomentum t ∈ chart)
    {e : ℂ} (he : e ∈ closedBall (scaledBand (realMomentum t)) (1 / 200))
    (hne : e ≠ scaledBand (realMomentum t))
    (R : SelfAdjointResolvent.BoundedInverse
      (materialFiber (scaledMomentum (realMomentum t)) (totalEnergy e) backgroundAmplitude)) :
    ‖R.map‖ ≤ ‖totalEnergy e - physicalBand (realMomentum t)‖⁻¹ + (2 : ℝ) ^ 112 := by
  have he' : ‖e - (Corner.lambdaStar : ℂ)‖ ≤ 1 / 50 := by
    have hn : ‖e - (Corner.lambdaStar : ℂ)‖ ≤ 1 / 100 := by
      simpa only [energyDisk, mem_closedBall, dist_eq_norm] using centeredEnergyDisk_subset ht he
    linarith
  rw [R.unique_map (inverseAwayFromBand ht he' hne),
    ← fullResolventExtension_eq_inverseAwayFromBand ht he' hne]
  exact fullResolventExtension_norm_le_real_band t ht he hne

end Maxwell.Continuum.PeriodicBand
