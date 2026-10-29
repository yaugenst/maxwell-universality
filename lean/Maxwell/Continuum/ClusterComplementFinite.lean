import Maxwell.Continuum.ClusterComplementLift
import Maxwell.Continuum.ClusterComplementDimension

/-!
# The actual sixteen-dimensional Schur operator

Restriction to the literal cluster is justified by proved invariance. Its
uniform correction bound is inherited from the full alias Hilbert space.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.ClusterComplement

open FreeFiber

instance : FiniteDimensional ℂ clusterSpace :=
  FiniteDimensional.of_finrank_pos (by rw [clusterSpace_finrank]; norm_num)

theorem clusterProjection_clusterPotential (u : FiberSpace) :
    clusterProjection (clusterPotential u) = clusterPotential u := by
  change clusterProjection (-(clusterProjection (potential (clusterProjection u)))) = _
  rw [map_neg, clusterProjection_idempotent]
  rfl

theorem clusterProjection_clusterVelocity (t : Momentum) (u : FiberSpace) :
    clusterProjection (clusterVelocity t u) = clusterVelocity t u := by
  apply Subtype.ext
  funext ν
  change clusterBlock ν (velocityBlock t ν (u ν)) = velocityBlock t ν (u ν)
  rw [velocityBlock_apply, map_smul]
  have hp : clusterBlock ν (clusterBlock ν (u ν)) = clusterBlock ν (u ν) :=
    congrArg (fun T : Polarization →L[ℂ] Polarization => T (u ν))
      (clusterBlock_isStarProjection ν).isIdempotentElem.eq
  rw [hp]

theorem clusterProjection_leadingCluster (t : Momentum) (e : ℂ) (u : FiberSpace) :
    clusterProjection (leadingCluster t e u) = leadingCluster t e u := by
  change clusterProjection (clusterPotential u + clusterVelocity t u - e • clusterProjection u) = _
  rw [map_sub, map_add, map_smul, clusterProjection_clusterPotential,
    clusterProjection_clusterVelocity, clusterProjection_idempotent]
  rfl

theorem clusterProjection_effectiveSchur (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) (u : FiberSpace) :
    clusterProjection (effectiveSchur t e ht he u) = effectiveSchur t e ht he u := by
  have h := schurLift_low_residual t e ht he u
  rw [schurLift_residual, map_smul] at h
  exact (smul_right_injective _
    (Complex.ofReal_ne_zero.mpr (ne_of_gt backgroundAmplitude_pos))) h

theorem clusterProjection_schurCorrection (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) (u : FiberSpace) :
    clusterProjection (schurCorrection t e ht he u) = schurCorrection t e ht he u := by
  have h := clusterProjection_effectiveSchur t e ht he u
  change clusterProjection (leadingCluster t e u +
    (backgroundAmplitude : ℂ) • schurCorrection t e ht he u) =
    leadingCluster t e u + (backgroundAmplitude : ℂ) • schurCorrection t e ht he u at h
  rw [map_add, map_smul, clusterProjection_leadingCluster] at h
  exact (smul_right_injective _
    (Complex.ofReal_ne_zero.mpr (ne_of_gt backgroundAmplitude_pos))) (add_left_cancel h)

def restrictToCluster (A : FiberSpace →L[ℂ] FiberSpace)
    (hA : ∀ u, clusterProjection (A u) = A u) : clusterSpace →L[ℂ] clusterSpace :=
  (A.codRestrict clusterSpace (fun u => (mem_clusterSpace_iff _).mpr (hA u))).comp
    clusterSpace.subtypeL

theorem restrictToCluster_apply (A : FiberSpace →L[ℂ] FiberSpace)
    (hA : ∀ u, clusterProjection (A u) = A u) (u : clusterSpace) :
    (restrictToCluster A hA u).val = A u.val := rfl

theorem restrictToCluster_norm_le (A : FiberSpace →L[ℂ] FiberSpace)
    (hA : ∀ u, clusterProjection (A u) = A u) : ‖restrictToCluster A hA‖ ≤ ‖A‖ := by
  apply (restrictToCluster A hA).opNorm_le_bound (norm_nonneg A)
  intro u
  change ‖A u.val‖ ≤ ‖A‖ * ‖u.val‖
  exact A.le_opNorm u.val

def finiteLeadingCluster (t : Momentum) (e : ℂ) : clusterSpace →L[ℂ] clusterSpace :=
  restrictToCluster (leadingCluster t e) (clusterProjection_leadingCluster t e)

def finiteCorrection (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) :
    clusterSpace →L[ℂ] clusterSpace :=
  restrictToCluster (schurCorrection t e ht he) (clusterProjection_schurCorrection t e ht he)

def finiteSchur (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) :
    clusterSpace →L[ℂ] clusterSpace :=
  restrictToCluster (effectiveSchur t e ht he) (clusterProjection_effectiveSchur t e ht he)

theorem finiteSchur_expansion (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) :
    finiteSchur t e ht he = finiteLeadingCluster t e +
      (backgroundAmplitude : ℂ) • finiteCorrection t e ht he := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  rfl

theorem finiteCorrection_norm_le_256 (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) :
    ‖finiteCorrection t e ht he‖ ≤ 256 :=
  (restrictToCluster_norm_le _ _).trans (schurCorrection_norm_le_256 t e ht he)

theorem finiteCorrection_norm_lt_129 (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) :
    ‖finiteCorrection t e ht he‖ < 129 :=
  (restrictToCluster_norm_le _ _).trans_lt (schurCorrection_norm_lt_129 t e ht he)

end Maxwell.Continuum.ClusterComplement
