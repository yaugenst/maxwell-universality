import Maxwell.Continuum.CalibrationSchurBasic

/-! The actual calibration Schur operator and its literal lift into the
full Maxwell domain. Its zero residual is an infinite-fiber statement. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.Calibration

open FreeFiber

variable (t : Momentum) (e : ℂ)
variable (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8)

def calibrationSchur : FiberSpace →L[ℂ] FiberSpace :=
  calibrationCentralMaterial t e-calibrationLeftCoupling*
    calibrationComplementInverse t e ht he*calibrationRightCoupling

def calibrationLift : FiberSpace →L[ℂ] FiberSpace :=
  centralAliasProjection-calibrationComplementInverse t e ht he*calibrationRightCoupling

theorem calibrationSchur_central (u : FiberSpace) :
    centralAliasProjection (calibrationSchur t e ht he u) = calibrationSchur t e ht he u := by
  change centralAliasProjection (calibrationCentralMaterial t e u-
    calibrationLeftCoupling (calibrationComplementInverse t e ht he (calibrationRightCoupling u))) = _
  rw [map_sub, calibrationCentralMaterial_central, calibrationLeftCoupling_central]
  rfl

theorem calibrationLift_mem_domain (u : FiberSpace) :
    calibrationLift t e ht he u ∈
      (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain :=
  (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain.sub_mem
    (centralAliasProjection_mem_domain _ _ u)
    (calibrationComplementInverse_mem_domain t e ht he (calibrationRightCoupling u))

theorem calibrationLift_central (u : FiberSpace) :
    centralAliasProjection (calibrationLift t e ht he u) = centralAliasProjection u := by
  change centralAliasProjection (centralAliasProjection u-
    calibrationComplementInverse t e ht he (calibrationRightCoupling u)) = _
  rw [map_sub, centralAliasProjection_idempotent, central_calibrationComplementInverse, sub_zero]

theorem calibrationComplementInverse_full_residual (f : FiberSpace) :
    materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude
      ⟨calibrationComplementInverse t e ht he f,
        calibrationComplementInverse_mem_domain t e ht he f⟩ =
      noncentralAliasProjection f+calibrationLeftCoupling (calibrationComplementInverse t e ht he f) := by
  have hlow := material_central_complement t e
    ⟨calibrationComplementInverse t e ht he f,calibrationComplementInverse_mem_domain t e ht he f⟩
    (central_calibrationComplementInverse t e ht he f)
  have hhigh := calibrationComplementInverse_apply t e ht he f
  change _-centralAliasProjection _ = _ at hhigh
  rw [hlow] at hhigh
  exact sub_eq_iff_eq_add.mp hhigh

theorem calibrationLift_residual (u : FiberSpace) :
    materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude
      ⟨calibrationLift t e ht he u,calibrationLift_mem_domain t e ht he u⟩ =
      calibrationSchur t e ht he u := by
  change (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).toFun
    ((⟨centralAliasProjection u,centralAliasProjection_mem_domain _ _ u⟩ :
      (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain) -
      ⟨calibrationComplementInverse t e ht he (calibrationRightCoupling u),
        calibrationComplementInverse_mem_domain t e ht he (calibrationRightCoupling u)⟩) = _
  rw [map_sub]
  change materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude
    ⟨centralAliasProjection u,_⟩ -
    materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude
      ⟨calibrationComplementInverse t e ht he (calibrationRightCoupling u),_⟩ = _
  rw [material_central_input, calibrationComplementInverse_full_residual,
    calibrationRightCoupling_noncentral]
  change calibrationCentralMaterial t e u+calibrationRightCoupling u-
    (calibrationRightCoupling u+calibrationLeftCoupling
      (calibrationComplementInverse t e ht he (calibrationRightCoupling u))) =
    calibrationCentralMaterial t e u-calibrationLeftCoupling
      (calibrationComplementInverse t e ht he (calibrationRightCoupling u))
  abel

def calibrationFiniteSchur : centralSpace →L[ℂ] centralSpace :=
  restrictCentral (calibrationSchur t e ht he) (calibrationSchur_central t e ht he)

theorem calibrationFiniteSchur_apply (u : centralSpace) :
    (calibrationFiniteSchur t e ht he u).val = calibrationSchur t e ht he u.val := rfl

theorem calibrationFiniteSchur_kernel_lifts (u : centralSpace)
    (hu : calibrationFiniteSchur t e ht he u = 0) :
    materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude
      ⟨calibrationLift t e ht he u.val,calibrationLift_mem_domain t e ht he u.val⟩ = 0 := by
  rw [calibrationLift_residual]
  exact congrArg Subtype.val hu

#print axioms calibrationLift_residual
#print axioms calibrationFiniteSchur_kernel_lifts

end Maxwell.Continuum.Calibration
