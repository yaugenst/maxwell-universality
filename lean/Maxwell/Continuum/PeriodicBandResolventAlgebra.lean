import Maxwell.Continuum.PeriodicBandSeparatedBounds
import Maxwell.Continuum.FreeFiberResolventIdentity

/-! Actual pole/complement algebra for the full continuum resolvent. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber FiberAnalytic FiberNormalization Metric Set

def physicalDelta (t : Momentum) (e : ℂ) : ℂ :=
  (backgroundAmplitude : ℂ) * (e - scaledBand t)

def fullBandComplement (t : Momentum) : FiberMap := 1 - fullSpectralProjection t

theorem physicalDelta_ne_zero {t : Momentum} {e : ℂ} (hne : e ≠ scaledBand t) :
    physicalDelta t e ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.mpr backgroundAmplitude_pos.ne') (sub_ne_zero.mpr hne)

theorem energyDisk_wide {e : ℂ} (he : e ∈ energyDisk) :
    ‖e - (Corner.lambdaStar : ℂ)‖ ≤ 1 / 50 := by
  have hn : ‖e - (Corner.lambdaStar : ℂ)‖ ≤ 1 / 100 := by
    simpa only [energyDisk, mem_closedBall, dist_eq_norm] using he
  linarith

theorem fullResolvent_on_kernel {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : e ∈ energyDisk) (hne : e ≠ scaledBand t) (u : FiberSpace) (hu : u ∈ physicalKernel t) :
    fullResolventExtension (t, e) u = -(physicalDelta t e)⁻¹ • u := by
  have h := inverse_scaled_on_kernel (scaledMomentum t) (totalEnergy e) (physicalBand t)
    backgroundAmplitude (inverseAwayFromBand ht (energyDisk_wide he) hne) u
    ((mem_physicalKernel_iff t u).mp hu)
  rw [← fullResolventExtension_eq_inverseAwayFromBand ht (energyDisk_wide he) hne] at h
  change (totalEnergy e - totalEnergy (scaledBand t)) • fullResolventExtension (t, e) u = -u at h
  rw [totalEnergy_sub] at h
  change physicalDelta t e • fullResolventExtension (t, e) u = -u at h
  have hh := congrArg (fun v : FiberSpace => (physicalDelta t e)⁻¹ • v) h
  rw [smul_smul, inv_mul_cancel₀ (physicalDelta_ne_zero hne), one_smul, smul_neg] at hh
  exact hh.trans (neg_smul _ _).symm

theorem fullResolvent_bilinear_symmetric {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : e ∈ energyDisk) (hne : e ≠ scaledBand t) (u v : FiberSpace) :
    bilinear (fullResolventExtension (t, e) u) v = bilinear u (fullResolventExtension (t, e) v) := by
  rw [fullResolventExtension_eq_inverseAwayFromBand ht (energyDisk_wide he) hne]
  exact inverse_bilinear_symmetric (scaledMomentum t) (totalEnergy e) backgroundAmplitude _ u v

theorem fullResolvent_mul_projection {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : e ∈ energyDisk) (hne : e ≠ scaledBand t) :
    fullResolventExtension (t, e) * fullSpectralProjection t =
      -(physicalDelta t e)⁻¹ • fullSpectralProjection t := by
  apply ContinuousLinearMap.ext
  intro u
  apply fullResolvent_on_kernel ht he hne
  rw [← fullSpectralProjection_range ht]
  exact ⟨u, rfl⟩

theorem projection_mul_fullResolvent {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : e ∈ energyDisk) (hne : e ≠ scaledBand t) :
    fullSpectralProjection t * fullResolventExtension (t, e) =
      -(physicalDelta t e)⁻¹ • fullSpectralProjection t := by
  apply ContinuousLinearMap.ext
  intro u
  rw [fullSpectralProjection_eq_bilinearProjection ht]
  change bilinear (normalizedFiberVector t) (fullResolventExtension (t, e) u) • normalizedFiberVector t =
    -(physicalDelta t e)⁻¹ • (bilinear (normalizedFiberVector t) u • normalizedFiberVector t)
  rw [← fullResolvent_bilinear_symmetric ht he hne,
    fullResolvent_on_kernel ht he hne (normalizedFiberVector t)
      ((mem_physicalKernel_iff t _).mpr (normalizedFiberVector_graph ht)),
    map_smul, smul_apply, smul_smul]
  rfl

theorem fullSeparated_eq_resolvent_complement {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : e ∈ energyDisk) (hne : e ≠ scaledBand t) :
    fullSeparatedResolvent t e = fullResolventExtension (t, e) * fullBandComplement t := by
  have hQ : fullResolventExtension (t, e) * fullBandComplement t =
      fullResolventExtension (t, e) - fullResolventExtension (t, e) * fullSpectralProjection t := by
    rw [fullBandComplement, mul_sub, mul_one]
  rw [fullSeparatedResolvent_eq_sub_pole ht he hne, hQ, fullResolvent_mul_projection ht he hne]
  apply ContinuousLinearMap.ext
  intro u
  change fullResolventExtension (t, e) u - (physicalDelta t e)⁻¹ • fullPoleResidue t u =
    fullResolventExtension (t, e) u - (-(physicalDelta t e)⁻¹) • (-(fullPoleResidue t u))
  rw [neg_smul, smul_neg, neg_neg]

theorem fullSeparated_eq_complement_resolvent {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : e ∈ energyDisk) (hne : e ≠ scaledBand t) :
    fullSeparatedResolvent t e = fullBandComplement t * fullResolventExtension (t, e) := by
  have hQ : fullBandComplement t * fullResolventExtension (t, e) =
      fullResolventExtension (t, e) - fullSpectralProjection t * fullResolventExtension (t, e) := by
    rw [fullBandComplement, sub_mul, one_mul]
  rw [fullSeparatedResolvent_eq_sub_pole ht he hne, hQ, projection_mul_fullResolvent ht he hne]
  apply ContinuousLinearMap.ext
  intro u
  change fullResolventExtension (t, e) u - (physicalDelta t e)⁻¹ • fullPoleResidue t u =
    fullResolventExtension (t, e) u - (-(physicalDelta t e)⁻¹) • (-(fullPoleResidue t u))
  rw [neg_smul, smul_neg, neg_neg]

theorem fullBandComplement_idempotent {t : Momentum} (ht : t ∈ chart) :
    fullBandComplement t * fullBandComplement t = fullBandComplement t := by
  unfold fullBandComplement
  simp only [mul_sub, sub_mul, mul_one, one_mul, fullSpectralProjection_idempotent ht]
  abel

theorem fullResolvent_identity {t : Momentum} (ht : t ∈ chart) {e f : ℂ}
    (he : e ∈ energyDisk) (hf : f ∈ energyDisk)
    (hne : e ≠ scaledBand t) (hnf : f ≠ scaledBand t) :
    fullResolventExtension (t, e) - fullResolventExtension (t, f) =
      ((backgroundAmplitude : ℂ) * (e - f)) •
        (fullResolventExtension (t, e) * fullResolventExtension (t, f)) := by
  rw [fullResolventExtension_eq_inverseAwayFromBand ht (energyDisk_wide he) hne,
    fullResolventExtension_eq_inverseAwayFromBand ht (energyDisk_wide hf) hnf]
  exact (material_resolvent_identity (scaledMomentum t) (totalEnergy e) (totalEnergy f)
    backgroundAmplitude _ _).trans (by rw [totalEnergy_sub])

theorem fullResolvent_identity_rev {t : Momentum} (ht : t ∈ chart) {e f : ℂ}
    (he : e ∈ energyDisk) (hf : f ∈ energyDisk)
    (hne : e ≠ scaledBand t) (hnf : f ≠ scaledBand t) :
    fullResolventExtension (t, e) - fullResolventExtension (t, f) =
      ((backgroundAmplitude : ℂ) * (e - f)) •
        (fullResolventExtension (t, f) * fullResolventExtension (t, e)) := by
  rw [fullResolventExtension_eq_inverseAwayFromBand ht (energyDisk_wide he) hne,
    fullResolventExtension_eq_inverseAwayFromBand ht (energyDisk_wide hf) hnf]
  exact (material_resolvent_identity_rev (scaledMomentum t) (totalEnergy e) (totalEnergy f)
    backgroundAmplitude _ _).trans (by rw [totalEnergy_sub])

end Maxwell.Continuum.PeriodicBand
