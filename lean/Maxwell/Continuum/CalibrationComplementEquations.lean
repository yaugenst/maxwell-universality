import Maxwell.Continuum.CalibrationCentral

/-! Both compression inverse laws for the actual infinite calibration
complement, on its full momentum-dependent maximal domain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.Calibration

open FreeFiber SelfAdjointResolvent
open scoped Classical

theorem calibrationFree_compression (t : Momentum) (e : ℂ) (u : FiberSpace)
    (hu : u ∈ (calibrationFree t e).domain)
    (hQu : noncentralAliasProjection u ∈ (operator (scaledMomentum t) (totalEnergy e)).domain) :
    calibrationFree t e ⟨u,hu⟩ = noncentralAliasProjection
      (operator (scaledMomentum t) (totalEnergy e) ⟨noncentralAliasProjection u,hQu⟩) +
      centralAliasProjection u := by
  apply Subtype.ext
  funext ν
  change calibrationFreeBlock t e ν (u ν) =
    noncentralAliasProjection (operator (scaledMomentum t) (totalEnergy e)
      ⟨noncentralAliasProjection u,hQu⟩) ν + centralAliasProjection u ν
  rw [noncentralAliasProjection_apply, centralAliasProjection_apply]
  change calibrationFreeBlock t e ν (u ν) =
    (if IsCentralAlias ν then 0 else block (aliasMomentum (scaledMomentum t) ν)
      (totalEnergy e) (noncentralAliasProjection u ν)) + (if IsCentralAlias ν then u ν else 0)
  rw [noncentralAliasProjection_apply]
  unfold calibrationFreeBlock
  split_ifs <;> simp

theorem calibrationMaterial_compression (t : Momentum) (e : ℂ) (u : FiberSpace)
    (hu : u ∈ (calibrationMaterial t e).domain)
    (hQu : noncentralAliasProjection u ∈ (operator (scaledMomentum t) (totalEnergy e)).domain) :
    calibrationMaterial t e ⟨u,hu⟩ = noncentralAliasProjection
      (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude
        ⟨noncentralAliasProjection u,hQu⟩) + centralAliasProjection u := by
  change calibrationFree t e ⟨u,hu⟩ + calibrationMaterialPerturbation u = _
  rw [calibrationFree_compression t e u hu hQu, materialFiber_apply]
  change noncentralAliasProjection (operator (scaledMomentum t) (totalEnergy e)
    ⟨noncentralAliasProjection u,hQu⟩) + centralAliasProjection u +
      -(backgroundAmplitude : ℂ) • noncentralAliasProjection (potential (noncentralAliasProjection u)) = _
  rw [map_sub, map_smul, neg_smul]
  simp only [sub_eq_add_neg, add_comm, add_left_comm]

theorem calibrationMaterial_central (t : Momentum) (e : ℂ)
    (u : (calibrationMaterial t e).domain) :
    centralAliasProjection (calibrationMaterial t e u) = centralAliasProjection u.val := by
  have hu : u.val ∈ (operator (scaledMomentum t) (totalEnergy e)).domain := by
    rw [← calibrationMaterial_domain t e]
    exact u.property
  rw [calibrationMaterial_compression t e u.val u.property
    (noncentralAliasProjection_mem_domain _ _ ⟨u.val,hu⟩), map_add,
    centralAliasProjection_noncentral, centralAliasProjection_idempotent, zero_add]

theorem calibrationMaterialInverse_norm (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8) :
    ‖(calibrationMaterialInverse t e ht he).map‖ ≤ 2 := by
  have hprod : ‖calibrationMaterialPerturbation*(calibrationFreeInverse t e ht he).map‖ ≤ 1/2 :=
    (calibration_product_norm t e ht he).trans calibration_ratio_le_half
  have hi : (1-‖calibrationMaterialPerturbation*(calibrationFreeInverse t e ht he).map‖)⁻¹ ≤ (2 : ℝ) := by
    have h := (inv_le_inv₀ (by linarith : 0 <
      1-‖calibrationMaterialPerturbation*(calibrationFreeInverse t e ht he).map‖)
      (by norm_num : (0 : ℝ) < 1/2)).mpr (by linarith)
    norm_num at h
    exact h
  exact (FreeFiber.Neumann.perturbationInverse_norm_le _ _ _ _).trans
    ((mul_le_mul (calibrationFreeInverse_norm t e ht he) hi
      (inv_nonneg.mpr (by linarith)) zero_le_one).trans
      (by norm_num))

def calibrationComplementInverse (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8) : FiberSpace →L[ℂ] FiberSpace :=
  (calibrationMaterialInverse t e ht he).map*noncentralAliasProjection

theorem calibrationComplementInverse_norm (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8) :
    ‖calibrationComplementInverse t e ht he‖ ≤ 2 := by
  exact (norm_mul_le _ _).trans ((mul_le_mul (calibrationMaterialInverse_norm t e ht he)
    noncentralAliasProjection_norm (norm_nonneg _) (by norm_num)).trans (by norm_num))

theorem calibrationComplementInverse_mem_domain (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8) (f : FiberSpace) :
    calibrationComplementInverse t e ht he f ∈
      (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain := by
  rw [materialFiber_domain, ← calibrationMaterial_domain t e]
  exact (calibrationMaterialInverse t e ht he).mem_domain (noncentralAliasProjection f)

@[simp] theorem central_calibrationComplementInverse (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8) (f : FiberSpace) :
    centralAliasProjection (calibrationComplementInverse t e ht he f) = 0 := by
  have h := congrArg centralAliasProjection
    ((calibrationMaterialInverse t e ht he).apply_map (noncentralAliasProjection f))
  rw [calibrationMaterial_central, centralAliasProjection_noncentral] at h
  exact h

@[simp] theorem noncentral_calibrationComplementInverse (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8) (f : FiberSpace) :
    noncentralAliasProjection (calibrationComplementInverse t e ht he f) =
      calibrationComplementInverse t e ht he f := by
  change calibrationComplementInverse t e ht he f-
    centralAliasProjection (calibrationComplementInverse t e ht he f) = _
  rw [central_calibrationComplementInverse, sub_zero]

theorem calibrationComplementInverse_apply (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8) (f : FiberSpace) :
    noncentralAliasProjection
      (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude
        ⟨calibrationComplementInverse t e ht he f,
          calibrationComplementInverse_mem_domain t e ht he f⟩) = noncentralAliasProjection f := by
  have h := (calibrationMaterialInverse t e ht he).apply_map (noncentralAliasProjection f)
  have hmem := calibrationComplementInverse_mem_domain t e ht he f
  have hQmem := noncentralAliasProjection_mem_domain (scaledMomentum t) (totalEnergy e)
    ⟨calibrationComplementInverse t e ht he f,hmem⟩
  change calibrationMaterial t e ⟨calibrationComplementInverse t e ht he f,_⟩ = _ at h
  rw [calibrationMaterial_compression t e _ _ hQmem] at h
  have hsub : (⟨noncentralAliasProjection (calibrationComplementInverse t e ht he f),hQmem⟩ :
    (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain) =
      ⟨calibrationComplementInverse t e ht he f,hmem⟩ :=
    Subtype.ext (noncentral_calibrationComplementInverse t e ht he f)
  rw [hsub, central_calibrationComplementInverse, add_zero] at h
  exact h

theorem calibrationComplementInverse_map_apply (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8)
    (u : (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain)
    (hu : noncentralAliasProjection u.val = u.val) :
    calibrationComplementInverse t e ht he
      (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude u) = u.val := by
  have hmem : u.val ∈ (calibrationMaterial t e).domain := by
    rw [calibrationMaterial_domain t e]
    exact u.property
  have h := (calibrationMaterialInverse t e ht he).map_apply ⟨u.val,hmem⟩
  have hQmem := noncentralAliasProjection_mem_domain (scaledMomentum t) (totalEnergy e) u
  have hsub : (⟨noncentralAliasProjection u.val,hQmem⟩ :
    (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain) = u :=
    Subtype.ext hu
  have hp : centralAliasProjection u.val = 0 := sub_eq_self.mp hu
  rw [calibrationMaterial_compression t e _ _ hQmem, hsub, hp, add_zero] at h
  exact h

#print axioms calibrationComplementInverse_apply
#print axioms calibrationComplementInverse_map_apply

end Maxwell.Continuum.Calibration
