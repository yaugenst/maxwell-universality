import Maxwell.Continuum.FiberNormalizationConjugation
import Maxwell.Continuum.FiberNormalizationScalar
import Maxwell.Continuum.PeriodicBandVector

/-! The actual infinite-fiber vector has a fixed real gauge and lies in
the quantitative neighborhood on which bilinear normalization is analytic. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.FiberNormalization

open FreeFiber ClusterComplement FiberAnalytic PeriodicPerturbation CornerBridge PeriodicBand

attribute [local irreducible] perturbation finiteK RankOneBand.Data.bandRoot
  scaledBand clusterVector

theorem polarization_inner_star (v w : Polarization) :
    inner ℂ (star v) (star w) = star (inner ℂ v w) := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply,
    polarization_star_apply, star_star, star_sum, star_mul']

theorem fiber_inner_star (v w : FiberSpace) :
    inner ℂ (star v) (star w) = star (inner ℂ v w) := by
  simp only [lp.inner_eq_tsum, fiber_star_apply, polarization_inner_star, tsum_star]

theorem packReal_star (v : Corner.ClusterField) : star (packReal v) = packReal v := by
  apply lp.ext
  funext ν
  apply PiLp.ext
  intro j
  by_cases hν : IsCentralAlias ν
  · simp [packReal, pack, realCube, momentumVector, realMomentum, hν]
  · simp [packReal, pack, hν]

theorem topState_star : star topState.val = topState.val :=
  packReal_star Corner.normalizedClusterVector

theorem clusterVector_gauge (t : Momentum) : inner ℂ topState (clusterVector t) = 1 := by
  unfold clusterVector RankOneBand.Data.bandVector
  exact actualCornerData.coefficient_eigenvectorLift _ _

theorem fiberVector_gauge {t : Momentum} (ht : t ∈ chart) :
    inner ℂ topState.val (fiberVector t) = 1 := by
  have hp := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    clusterProjection_isStarProjection.isSelfAdjoint) topState.val (fiberVector t)
  change inner ℂ (clusterProjection topState.val) (fiberVector t) =
    inner ℂ topState.val (clusterProjection (fiberVector t)) at hp
  rw [(mem_clusterSpace_iff _).mp topState.property, clusterProjection_fiberVector ht] at hp
  exact hp.trans (clusterVector_gauge t)

theorem fiberVector_complement_bound {t : Momentum} (ht : t ∈ chart) :
    ‖fiberVector t - (clusterVector t).val‖ ≤ 32 * backgroundAmplitude := by
  have hb := chart_energy_inBox ht (scaledBand_mem ht)
  have hP := (mem_clusterSpace_iff _).mp (clusterVector t).property
  rw [fiberVector_eq ht, schurLift, sub_apply,
    mul_apply_eq_comp, hP, sub_sub_cancel_left, norm_neg]
  have hR := complementInverse_norm_le t (scaledBand t) hb.1 hb.2
  have hB := rightCoupling_norm_le t (totalEnergy (scaledBand t)) hb.1
  have hc := clusterVector_norm_le ht
  have hbv := (rightCoupling t (totalEnergy (scaledBand t)) hb.1).le_opNorm
    (clusterVector t).val
  have hrv := (complementInverse t (scaledBand t) hb.1 hb.2).le_opNorm
    (rightCoupling t (totalEnergy (scaledBand t)) hb.1 (clusterVector t).val)
  have hbv' : ‖rightCoupling t (totalEnergy (scaledBand t)) hb.1 (clusterVector t).val‖ ≤
      16 * backgroundAmplitude := by
    apply hbv.trans
    have h := mul_le_mul hB hc (norm_nonneg _)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) backgroundAmplitude_pos.le)
    change ‖rightCoupling t (totalEnergy (scaledBand t)) hb.1‖ * ‖clusterVector t‖ ≤ _
    nlinarith
  exact hrv.trans (by
    have h := mul_le_mul hR hbv' (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith)

theorem fiberVector_sub_top_bound {t : Momentum} (ht : t ∈ chart) :
    ‖fiberVector t - topState.val‖ ≤ 1 / 5 := by
  have h1 := fiberVector_complement_bound ht
  have h2 := clusterVector_sub_top_bound ht
  have htri := norm_add_le (fiberVector t - (clusterVector t).val)
    ((clusterVector t).val - topState.val)
  rw [sub_add_sub_cancel] at htri
  change ‖(clusterVector t).val - topState.val‖ ≤ 5 / 32 at h2
  have hρ := backgroundAmplitude_le
  linarith

theorem fiberVector_bilinear_bound {t : Momentum} (ht : t ∈ chart) :
    ‖bilinear (fiberVector t) (fiberVector t) - 1‖ ≤ 11 / 25 :=
  bilinear_near_unit topState.val (fiberVector t) topState_star topState_norm
    (fiberVector_sub_top_bound ht)

theorem fiberVector_bilinear_ne_zero {t : Momentum} (ht : t ∈ chart) :
    bilinear (fiberVector t) (fiberVector t) ≠ 0 :=
  near_one_ne_zero _ (fiberVector_bilinear_bound ht)

#print axioms fiberVector_gauge
#print axioms fiberVector_bilinear_bound

end Maxwell.Continuum.FiberNormalization
