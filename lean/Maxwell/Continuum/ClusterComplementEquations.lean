import Maxwell.Continuum.ClusterComplementMaterial

/-!
# Inverse of the literal complementary Maxwell fiber

The bounded inverse maps into the actual maximal domain at the specified
complex momentum, lies in the fixed complementary subspace, and satisfies
both inverse laws for `Q (A - ρ V) Q` on that subspace.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.ClusterComplement

open FreeFiber SelfAdjointResolvent

@[simp]
theorem clusterProjection_idempotent (u : FiberSpace) :
    clusterProjection (clusterProjection u) = clusterProjection u :=
  congrArg (fun T : FiberSpace →L[ℂ] FiberSpace => T u)
    clusterProjection_isStarProjection.isIdempotentElem.eq

@[simp]
theorem complementProjection_idempotent (u : FiberSpace) :
    complementProjection (complementProjection u) = complementProjection u :=
  congrArg (fun T : FiberSpace →L[ℂ] FiberSpace => T u)
    complementProjection_isStarProjection.isIdempotentElem.eq

@[simp]
theorem clusterProjection_complementProjection (u : FiberSpace) :
    clusterProjection (complementProjection u) = 0 := by
  change clusterProjection (u - clusterProjection u) = 0
  rw [map_sub, clusterProjection_idempotent, sub_self]

@[simp]
theorem complementProjection_clusterProjection (u : FiberSpace) :
    complementProjection (clusterProjection u) = 0 := by
  change clusterProjection u - clusterProjection (clusterProjection u) = 0
  rw [clusterProjection_idempotent, sub_self]

theorem complementProjection_eq_self_iff (u : FiberSpace) :
    complementProjection u = u ↔ clusterProjection u = 0 := by
  change u - clusterProjection u = u ↔ _
  exact sub_eq_self

theorem regularizedFree_compression (t : Momentum) (e : ℂ) (u : FiberSpace)
    (hu : u ∈ (regularizedFree t e).domain)
    (hQu : complementProjection u ∈ (operator (scaledMomentum t) (totalEnergy e)).domain) :
    regularizedFree t e ⟨u, hu⟩ =
      complementProjection (operator (scaledMomentum t) (totalEnergy e)
        ⟨complementProjection u, hQu⟩) + clusterProjection u := by
  apply Subtype.ext
  funext ν
  rfl

theorem regularizedMaterial_compression (t : Momentum) (e : ℂ) (u : FiberSpace)
    (hu : u ∈ (regularizedMaterial t e).domain)
    (hQu : complementProjection u ∈ (operator (scaledMomentum t) (totalEnergy e)).domain) :
    regularizedMaterial t e ⟨u, hu⟩ =
      complementProjection (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude
        ⟨complementProjection u, hQu⟩) + clusterProjection u := by
  change regularizedFree t e ⟨u, hu⟩ + compressedMaterial u = _
  rw [regularizedFree_compression t e u hu hQu, materialFiber_apply]
  change complementProjection (operator (scaledMomentum t) (totalEnergy e)
      ⟨complementProjection u, hQu⟩) + clusterProjection u +
      -(backgroundAmplitude : ℂ) • complementProjection (potential (complementProjection u)) = _
  rw [map_sub, map_smul, neg_smul]
  simp only [sub_eq_add_neg, add_comm, add_left_comm]

theorem regularizedMaterial_clusterProjection (t : Momentum) (e : ℂ)
    (u : (regularizedMaterial t e).domain) :
    clusterProjection (regularizedMaterial t e u) = clusterProjection u.val := by
  have hu : u.val ∈ (operator (scaledMomentum t) (totalEnergy e)).domain := by
    rw [← regularizedMaterial_domain t e]
    exact u.property
  rw [regularizedMaterial_compression t e u.val u.property
    (complementProjection_mem_domain _ _ ⟨u.val, hu⟩), map_add,
    clusterProjection_complementProjection, clusterProjection_idempotent, zero_add]

def complementInverse (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) :
    FiberSpace →L[ℂ] FiberSpace :=
  (regularizedMaterialInverse t e ht he).map * complementProjection

theorem complementInverse_norm_le (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) :
    ‖complementInverse t e ht he‖ ≤ 2 := by
  exact (norm_mul_le _ _).trans ((mul_le_mul
    (regularizedMaterialInverse_norm_le t e ht he) complementProjection_norm_le
    (norm_nonneg _) (by norm_num)).trans (by norm_num))

theorem complementInverse_mem_domain (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) (f : FiberSpace) :
    complementInverse t e ht he f ∈
      (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain := by
  rw [materialFiber_domain, ← regularizedMaterial_domain t e]
  exact (regularizedMaterialInverse t e ht he).mem_domain (complementProjection f)

@[simp]
theorem clusterProjection_complementInverse (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) (f : FiberSpace) :
    clusterProjection (complementInverse t e ht he f) = 0 := by
  have h := congrArg clusterProjection
    ((regularizedMaterialInverse t e ht he).apply_map (complementProjection f))
  rw [regularizedMaterial_clusterProjection, clusterProjection_complementProjection] at h
  exact h

@[simp]
theorem complementProjection_complementInverse (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) (f : FiberSpace) :
    complementProjection (complementInverse t e ht he f) = complementInverse t e ht he f :=
  (complementProjection_eq_self_iff _).mpr (clusterProjection_complementInverse t e ht he f)

theorem complementInverse_apply (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) (f : FiberSpace) :
    complementProjection (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude
      ⟨complementInverse t e ht he f, complementInverse_mem_domain t e ht he f⟩) =
      complementProjection f := by
  have h := (regularizedMaterialInverse t e ht he).apply_map (complementProjection f)
  have hmem := complementInverse_mem_domain t e ht he f
  have hQmem := complementProjection_mem_domain (scaledMomentum t) (totalEnergy e)
    ⟨complementInverse t e ht he f, hmem⟩
  change complementProjection (complementInverse t e ht he f) ∈
    (operator (scaledMomentum t) (totalEnergy e)).domain at hQmem
  change regularizedMaterial t e ⟨complementInverse t e ht he f, _⟩ =
    complementProjection f at h
  rw [regularizedMaterial_compression t e _ _ hQmem] at h
  have hsub : (⟨complementProjection (complementInverse t e ht he f), hQmem⟩ :
      (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain) =
      ⟨complementInverse t e ht he f, hmem⟩ :=
    Subtype.ext (complementProjection_complementInverse t e ht he f)
  rw [hsub, clusterProjection_complementInverse, add_zero] at h
  exact h

theorem complementInverse_map_apply (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8)
    (u : (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain)
    (hu : complementProjection u.val = u.val) :
    complementInverse t e ht he
      (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude u) = u.val := by
  have hmem : u.val ∈ (regularizedMaterial t e).domain := by
    rw [regularizedMaterial_domain t e]
    exact u.property
  have h := (regularizedMaterialInverse t e ht he).map_apply ⟨u.val, hmem⟩
  have hQmem := complementProjection_mem_domain (scaledMomentum t) (totalEnergy e) u
  have hsub : (⟨complementProjection u.val, hQmem⟩ :
      (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain) = u :=
    Subtype.ext hu
  rw [regularizedMaterial_compression t e _ _ hQmem, hsub,
    (complementProjection_eq_self_iff _).mp hu, add_zero] at h
  exact h

end Maxwell.Continuum.ClusterComplement
