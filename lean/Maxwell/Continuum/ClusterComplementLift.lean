import Maxwell.Continuum.ClusterComplementSchur

/-!
# Lifting the finite Schur equation to the actual infinite fiber

The explicit lift belongs to the original maximal domain and its full
Maxwell residual is exactly the scaled Schur residual. Its complementary
residual vanishes by the constructed infinite inverse.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.ClusterComplement

open FreeFiber

theorem rightCoupling_complementProjection (t : Momentum) (E : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (u : FiberSpace) :
    complementProjection (rightCoupling t E ht u) = rightCoupling t E ht u := by
  rw [rightCoupling_apply, complementProjection_idempotent]

theorem leftCoupling_on_complement (t : Momentum) (E : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹)
    (u : (operator (scaledMomentum t) E).domain) (hu : complementProjection u.val = u.val) :
    leftCoupling t E ht u.val =
      clusterProjection (materialFiber (scaledMomentum t) E backgroundAmplitude u) := by
  rw [leftCoupling_apply]
  have hsub : (⟨complementProjection u.val, complementProjection_mem_domain _ _ u⟩ :
      (materialFiber (scaledMomentum t) E backgroundAmplitude).domain) = u := Subtype.ext hu
  rw [hsub]

def schurLift (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) : FiberSpace →L[ℂ] FiberSpace :=
  clusterProjection - complementInverse t e ht he * rightCoupling t (totalEnergy e) ht

theorem schurLift_mem_domain (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) (u : FiberSpace) :
    schurLift t e ht he u ∈
      (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain :=
  (operator (scaledMomentum t) (totalEnergy e)).domain.sub_mem
    (clusterProjection_mem_domain _ _ u)
    (complementInverse_mem_domain t e ht he (rightCoupling t (totalEnergy e) ht u))

theorem materialFiber_schurLift (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) (u : FiberSpace) :
    materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude
      ⟨schurLift t e ht he u, schurLift_mem_domain t e ht he u⟩ =
      materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude
        ⟨clusterProjection u, clusterProjection_mem_domain _ _ u⟩ -
      materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude
        ⟨complementInverse t e ht he (rightCoupling t (totalEnergy e) ht u),
          complementInverse_mem_domain t e ht he _⟩ := by
  exact (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).toFun.map_sub
    ⟨clusterProjection u, clusterProjection_mem_domain _ _ u⟩
    ⟨complementInverse t e ht he (rightCoupling t (totalEnergy e) ht u),
      complementInverse_mem_domain t e ht he _⟩

theorem schurLift_high_residual (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) (u : FiberSpace) :
    complementProjection (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude
      ⟨schurLift t e ht he u, schurLift_mem_domain t e ht he u⟩) = 0 := by
  rw [materialFiber_schurLift, map_sub, ← rightCoupling_apply t (totalEnergy e) ht u,
    complementInverse_apply, rightCoupling_complementProjection, sub_self]

theorem schurLift_low_residual (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) (u : FiberSpace) :
    clusterProjection (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude
      ⟨schurLift t e ht he u, schurLift_mem_domain t e ht he u⟩) =
      (backgroundAmplitude : ℂ) • effectiveSchur t e ht he u := by
  have hl := leftCoupling_on_complement t (totalEnergy e) ht
    ⟨complementInverse t e ht he (rightCoupling t (totalEnergy e) ht u),
      complementInverse_mem_domain t e ht he _⟩
    (complementProjection_complementInverse t e ht he _)
  rw [materialFiber_schurLift, map_sub, ← lowBlock_apply, ← hl]
  exact (congrArg (fun T : FiberSpace →L[ℂ] FiberSpace => T u)
    (effectiveSchur_exact t e ht he)).symm

/-- Exact full-fiber equation, with the original momentum-dependent domain. -/
theorem schurLift_residual (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) (u : FiberSpace) :
    materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude
      ⟨schurLift t e ht he u, schurLift_mem_domain t e ht he u⟩ =
      (backgroundAmplitude : ℂ) • effectiveSchur t e ht he u := by
  have hQ := schurLift_high_residual t e ht he u
  change _ - clusterProjection _ = 0 at hQ
  exact (sub_eq_zero.mp hQ).trans (schurLift_low_residual t e ht he u)

theorem clusterProjection_schurLift (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) (u : FiberSpace) :
    clusterProjection (schurLift t e ht he u) = clusterProjection u := by
  change clusterProjection (clusterProjection u -
    complementInverse t e ht he (rightCoupling t (totalEnergy e) ht u)) = _
  rw [map_sub, clusterProjection_idempotent, clusterProjection_complementInverse, sub_zero]

theorem schurLift_ne_zero (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) (u : FiberSpace)
    (hu : clusterProjection u = u) (hu0 : u ≠ 0) : schurLift t e ht he u ≠ 0 := by
  intro h
  have hp := congrArg clusterProjection h
  rw [clusterProjection_schurLift, hu, map_zero] at hp
  exact hu0 hp

theorem schur_kernel_lifts (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) (u : FiberSpace)
    (hu : effectiveSchur t e ht he u = 0) :
    materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude
      ⟨schurLift t e ht he u, schurLift_mem_domain t e ht he u⟩ = 0 := by
  rw [schurLift_residual, hu, smul_zero]

theorem complementInverse_complementProjection (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) (f : FiberSpace) :
    complementInverse t e ht he (complementProjection f) = complementInverse t e ht he f := by
  change (regularizedMaterialInverse t e ht he).map (complementProjection (complementProjection f)) = _
  rw [complementProjection_idempotent]
  rfl

theorem rightCoupling_clusterProjection (t : Momentum) (E : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (u : FiberSpace) :
    rightCoupling t E ht (clusterProjection u) = rightCoupling t E ht u := by
  rw [rightCoupling_apply, rightCoupling_apply]
  have hsub : (⟨clusterProjection (clusterProjection u), clusterProjection_mem_domain _ _ _⟩ :
      (materialFiber (scaledMomentum t) E backgroundAmplitude).domain) =
      ⟨clusterProjection u, clusterProjection_mem_domain _ _ _⟩ :=
    Subtype.ext (clusterProjection_idempotent u)
  rw [hsub]

theorem schurLift_clusterProjection (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) (u : FiberSpace) :
    schurLift t e ht he (clusterProjection u) = schurLift t e ht he u := by
  change clusterProjection (clusterProjection u) -
    complementInverse t e ht he (rightCoupling t (totalEnergy e) ht (clusterProjection u)) = _
  rw [clusterProjection_idempotent, rightCoupling_clusterProjection]
  rfl

theorem materialFiber_complementProjection (q : Momentum) (E : ℂ)
    (u : (materialFiber q E backgroundAmplitude).domain) :
    materialFiber q E backgroundAmplitude
      ⟨complementProjection u.val, complementProjection_mem_domain _ _ u⟩ =
      materialFiber q E backgroundAmplitude u - materialFiber q E backgroundAmplitude
        ⟨clusterProjection u.val, clusterProjection_mem_domain _ _ u.val⟩ :=
  (materialFiber q E backgroundAmplitude).toFun.map_sub u
    ⟨clusterProjection u.val, clusterProjection_mem_domain _ _ u.val⟩

/-- The complementary part of every actual fiber kernel vector is forced
by the infinite inverse; no regularity or common-domain premise is added. -/
theorem kernel_complement_eq (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8)
    (u : (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain)
    (hu : materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude u = 0) :
    complementProjection u.val =
      -(complementInverse t e ht he (rightCoupling t (totalEnergy e) ht u.val)) := by
  have hres : complementProjection (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude
      ⟨complementProjection u.val, complementProjection_mem_domain _ _ u⟩) =
      -(rightCoupling t (totalEnergy e) ht u.val) := by
    rw [materialFiber_complementProjection, hu, map_sub, map_zero, zero_sub,
      ← rightCoupling_apply t (totalEnergy e) ht u.val]
  have hinv := complementInverse_map_apply t e ht he
    ⟨complementProjection u.val, complementProjection_mem_domain _ _ u⟩
    (complementProjection_idempotent u.val)
  have h := congrArg (complementInverse t e ht he) hres
  rw [complementInverse_complementProjection, hinv, map_neg] at h
  exact h

theorem kernel_reconstruction (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8)
    (u : (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain)
    (hu : materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude u = 0) :
    schurLift t e ht he u.val = u.val := by
  change clusterProjection u.val -
    complementInverse t e ht he (rightCoupling t (totalEnergy e) ht u.val) = u.val
  calc
    _ = clusterProjection u.val + complementProjection u.val := by
      rw [kernel_complement_eq t e ht he u hu, sub_eq_add_neg]
    _ = u.val := by change clusterProjection u.val + (u.val - clusterProjection u.val) = u.val; abel

theorem kernel_projects_to_schur (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8)
    (u : (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain)
    (hu : materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude u = 0) :
    effectiveSchur t e ht he (clusterProjection u.val) = 0 := by
  have h := schurLift_residual t e ht he (clusterProjection u.val)
  have hsub : (⟨schurLift t e ht he (clusterProjection u.val), schurLift_mem_domain _ _ _ _ _⟩ :
      (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain) = u :=
    Subtype.ext ((schurLift_clusterProjection t e ht he u.val).trans
      (kernel_reconstruction t e ht he u hu))
  rw [hsub, hu] at h
  exact (smul_eq_zero.mp h.symm).resolve_left
    (Complex.ofReal_ne_zero.mpr (ne_of_gt backgroundAmplitude_pos))

theorem kernel_projection_ne_zero (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8)
    (u : (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain)
    (hu : materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude u = 0)
    (hu0 : u.val ≠ 0) : clusterProjection u.val ≠ 0 := by
  intro hP
  have h := schurLift_clusterProjection t e ht he u.val
  rw [hP, map_zero, kernel_reconstruction t e ht he u hu] at h
  exact hu0 h.symm

end Maxwell.Continuum.ClusterComplement
