import Maxwell.Continuum.CalibrationSchur

/-! Exact reconstruction for the 24-dimensional calibration split. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.Calibration

open FreeFiber

variable (t : Momentum) (e : ℂ)
variable (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8)

theorem calibrationComplementInverse_central (f : FiberSpace)
    (hf : centralAliasProjection f = f) : calibrationComplementInverse t e ht he f = 0 := by
  change (calibrationMaterialInverse t e ht he).map (f-centralAliasProjection f) = 0
  rw [hf,sub_self,map_zero]

theorem calibrationRightCoupling_central_input (f : FiberSpace) :
    calibrationRightCoupling (centralAliasProjection f) = calibrationRightCoupling f := by
  change -(backgroundAmplitude : ℂ) • noncentralAliasProjection
    (potential (centralAliasProjection (centralAliasProjection f))) = _
  rw [centralAliasProjection_idempotent]
  rfl

theorem calibrationCentralMaterial_central_input (f : FiberSpace) :
    calibrationCentralMaterial t e (centralAliasProjection f) = calibrationCentralMaterial t e f := by
  change centralFree t e (centralAliasProjection f)-(backgroundAmplitude : ℂ) •
    centralAliasProjection (potential (centralAliasProjection (centralAliasProjection f))) = _
  rw [centralFree_central,centralAliasProjection_idempotent]
  rfl

theorem calibrationSchur_central_input (f : FiberSpace) :
    calibrationSchur t e ht he (centralAliasProjection f) = calibrationSchur t e ht he f := by
  change calibrationCentralMaterial t e (centralAliasProjection f)-
    calibrationLeftCoupling (calibrationComplementInverse t e ht he
      (calibrationRightCoupling (centralAliasProjection f))) = _
  rw [calibrationCentralMaterial_central_input,calibrationRightCoupling_central_input]
  rfl

theorem calibrationLift_central_input (f : FiberSpace) :
    calibrationLift t e ht he (centralAliasProjection f) = calibrationLift t e ht he f := by
  change centralAliasProjection (centralAliasProjection f)-calibrationComplementInverse t e ht he
    (calibrationRightCoupling (centralAliasProjection f)) = _
  rw [centralAliasProjection_idempotent,calibrationRightCoupling_central_input]
  rfl

theorem calibration_complement_reconstruction
    (u : (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain) :
    calibrationComplementInverse t e ht he
      (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude u) =
      noncentralAliasProjection u.val+calibrationComplementInverse t e ht he (calibrationRightCoupling u.val) := by
  have hQmem := noncentralAliasProjection_mem_domain (scaledMomentum t) (totalEnergy e) u
  have hsub : (⟨noncentralAliasProjection u.val,hQmem⟩ :
    (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain) =
    u-⟨centralAliasProjection u.val,centralAliasProjection_mem_domain _ _ u.val⟩ := rfl
  have hb := calibrationComplementInverse_map_apply t e ht he
    ⟨noncentralAliasProjection u.val,hQmem⟩ (noncentralAliasProjection_idempotent u.val)
  have hmap : materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude
      (u-⟨centralAliasProjection u.val,centralAliasProjection_mem_domain _ _ u.val⟩) =
      materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude u-
        materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude
          ⟨centralAliasProjection u.val,centralAliasProjection_mem_domain _ _ u.val⟩ :=
    map_sub (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).toFun _ _
  rw [hsub,hmap] at hb
  change calibrationComplementInverse t e ht he
    (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude u-
      materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude
        ⟨centralAliasProjection u.val,_⟩) = _ at hb
  rw [material_central_input,map_sub,map_add,
    calibrationComplementInverse_central t e ht he _ (calibrationCentralMaterial_central t e u.val),
    zero_add] at hb
  exact sub_eq_iff_eq_add.mp hb

theorem calibration_reconstruction
    (u : (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain) :
    u.val = calibrationLift t e ht he u.val+calibrationComplementInverse t e ht he
      (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude u) := by
  rw [calibration_complement_reconstruction]
  change u.val = (centralAliasProjection u.val-calibrationComplementInverse t e ht he
    (calibrationRightCoupling u.val))+(u.val-centralAliasProjection u.val+
      calibrationComplementInverse t e ht he (calibrationRightCoupling u.val))
  abel

theorem calibration_kernel_reconstruction
    (u : (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain)
    (hu : materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude u = 0) :
    u.val = calibrationLift t e ht he u.val := by
  have h := calibration_reconstruction t e ht he u
  rw [hu,map_zero,add_zero] at h
  exact h

theorem calibration_kernel_projects
    (u : (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain)
    (hu : materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude u = 0) :
    calibrationSchur t e ht he (centralAliasProjection u.val) = 0 := by
  have hp := calibration_kernel_reconstruction t e ht he u hu
  have hsub : (⟨calibrationLift t e ht he u.val,calibrationLift_mem_domain t e ht he u.val⟩ :
    (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain) = u :=
      Subtype.ext hp.symm
  rw [calibrationSchur_central_input,← calibrationLift_residual,hsub,hu]

def centralProjectionToSpace : FiberSpace →L[ℂ] centralSpace :=
  centralAliasProjection.codRestrict centralSpace
    (fun u => (mem_centralSpace_iff _).mpr (centralAliasProjection_idempotent u))

theorem centralProjectionToSpace_norm : ‖centralProjectionToSpace‖ ≤ 1 := by
  apply centralProjectionToSpace.opNorm_le_bound (by norm_num)
  intro u
  exact centralAliasProjection.le_of_opNorm_le centralAliasProjection_norm u

theorem centralProjectionToSpace_coe (u : centralSpace) : centralProjectionToSpace u.val = u := by
  apply Subtype.ext
  exact (mem_centralSpace_iff _).mp u.property

theorem calibrationMaterial_injective_of_finite
    (hS : Function.Injective (calibrationFiniteSchur t e ht he)) :
    Function.Injective (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude) := by
  have hz (u : (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain)
      (hu : materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude u = 0) : u = 0 := by
    have hs : calibrationFiniteSchur t e ht he (centralProjectionToSpace u.val) = 0 := by
      apply Subtype.ext
      exact calibration_kernel_projects t e ht he u hu
    have hp0 := hS (hs.trans (map_zero _).symm)
    have hp : centralAliasProjection u.val = 0 := congrArg Subtype.val hp0
    have hr := calibration_kernel_reconstruction t e ht he u hu
    rw [← calibrationLift_central_input t e ht he u.val,hp,map_zero] at hr
    exact Subtype.ext hr
  intro u v huv
  apply sub_eq_zero.mp
  apply hz
  change (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).toFun (u-v) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr huv

#print axioms calibration_reconstruction
#print axioms calibrationMaterial_injective_of_finite

end Maxwell.Continuum.Calibration
