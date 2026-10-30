import Maxwell.Continuum.CalibrationKernel

/-! The finite calibration Schur inverse reconstructs a two-sided
inverse on the complete continuum Maxwell domain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.Calibration

open FreeFiber SelfAdjointResolvent

variable (t : Momentum) (e : ℂ)
variable (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8)

theorem calibrationLift_norm : ‖calibrationLift t e ht he‖ ≤ 2 := by
  have hb := (norm_sub_le centralAliasProjection
    (calibrationComplementInverse t e ht he*calibrationRightCoupling)).trans
      (add_le_add centralAliasProjection_norm ((norm_mul_le _ _).trans
        (mul_le_mul (calibrationComplementInverse_norm t e ht he)
          (calibrationRightCoupling_norm.trans calibration_ratio_le_half) (norm_nonneg _) (by norm_num))))
  exact hb.trans (by norm_num)

def calibrationAdjustedSource : FiberSpace →L[ℂ] centralSpace :=
  centralProjectionToSpace.comp (1-calibrationLeftCoupling*calibrationComplementInverse t e ht he)

theorem calibrationAdjustedSource_apply (f : FiberSpace) :
    (calibrationAdjustedSource t e ht he f).val = centralAliasProjection f-
      calibrationLeftCoupling (calibrationComplementInverse t e ht he f) := by
  change centralAliasProjection (f-calibrationLeftCoupling (calibrationComplementInverse t e ht he f)) = _
  rw [map_sub,calibrationLeftCoupling_central]

theorem calibrationAdjustedSource_norm : ‖calibrationAdjustedSource t e ht he‖ ≤ 2 := by
  have hc : ‖calibrationLeftCoupling*calibrationComplementInverse t e ht he‖ ≤ 1 :=
    (norm_mul_le _ _).trans ((mul_le_mul
      (calibrationLeftCoupling_norm.trans calibration_ratio_le_half)
      (calibrationComplementInverse_norm t e ht he) (norm_nonneg _) (by norm_num)).trans (by norm_num))
  have hs : ‖(1 : FiberSpace →L[ℂ] FiberSpace)-
      calibrationLeftCoupling*calibrationComplementInverse t e ht he‖ ≤ 2 :=
    (norm_sub_le _ _).trans ((add_le_add ContinuousLinearMap.norm_id_le hc).trans (by norm_num))
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans ((mul_le_mul
    centralProjectionToSpace_norm hs (norm_nonneg _) zero_le_one).trans (by norm_num))

def calibrationFullResolvent (J : centralSpace →L[ℂ] centralSpace) : FiberSpace →L[ℂ] FiberSpace :=
  calibrationComplementInverse t e ht he+
    (calibrationLift t e ht he).comp (centralSpace.subtypeL.comp
      (J.comp (calibrationAdjustedSource t e ht he)))

theorem calibrationFullResolvent_mem_domain (J : centralSpace →L[ℂ] centralSpace) (f : FiberSpace) :
    calibrationFullResolvent t e ht he J f ∈
      (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain :=
  Submodule.add_mem _ (calibrationComplementInverse_mem_domain t e ht he f)
    (calibrationLift_mem_domain t e ht he _)

theorem calibrationFullResolvent_norm (J : centralSpace →L[ℂ] centralSpace) :
    ‖calibrationFullResolvent t e ht he J‖ ≤ 2+4*‖J‖ := by
  have hc : ‖(calibrationLift t e ht he).comp (centralSpace.subtypeL.comp
      (J.comp (calibrationAdjustedSource t e ht he)))‖ ≤ 4*‖J‖ := by
    calc
      _ ≤ ‖calibrationLift t e ht he‖*(‖centralSpace.subtypeL‖*(‖J‖*‖calibrationAdjustedSource t e ht he‖)) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
          ((ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
            (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))) (norm_nonneg _))
      _ ≤ 2*(1*(‖J‖*2)) := by
        gcongr
        · exact calibrationLift_norm t e ht he
        · exact centralSpace.norm_subtypeL_le
        · exact calibrationAdjustedSource_norm t e ht he
      _ = _ := by ring
  exact (norm_add_le _ _).trans (add_le_add (calibrationComplementInverse_norm t e ht he) hc)

theorem calibrationFullResolvent_right (J : centralSpace →L[ℂ] centralSpace)
    (hJ : calibrationFiniteSchur t e ht he*J = 1) (f : FiberSpace) :
    materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude
      ⟨calibrationFullResolvent t e ht he J f,calibrationFullResolvent_mem_domain t e ht he J f⟩ = f := by
  have hs0 : calibrationFiniteSchur t e ht he (J (calibrationAdjustedSource t e ht he f)) =
      calibrationAdjustedSource t e ht he f :=
    congrArg (fun T : centralSpace →L[ℂ] centralSpace => T (calibrationAdjustedSource t e ht he f)) hJ
  have hs := congrArg Subtype.val hs0
  change (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).toFun
    ((⟨calibrationComplementInverse t e ht he f,calibrationComplementInverse_mem_domain t e ht he f⟩ :
      (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).domain)+
      ⟨calibrationLift t e ht he (J (calibrationAdjustedSource t e ht he f)).val,
        calibrationLift_mem_domain t e ht he _⟩) = f
  rw [map_add]
  change materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude
      ⟨calibrationComplementInverse t e ht he f,_⟩+
    materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude
      ⟨calibrationLift t e ht he (J (calibrationAdjustedSource t e ht he f)).val,_⟩ = f
  rw [calibrationLift_residual,← calibrationFiniteSchur_apply,hs,calibrationAdjustedSource_apply,
    calibrationComplementInverse_full_residual]
  change (f-centralAliasProjection f)+_+(centralAliasProjection f-_) = f
  abel

def calibrationInverseFromFinite (J : centralSpace →L[ℂ] centralSpace)
    (hr : calibrationFiniteSchur t e ht he*J = 1) (hl : J*calibrationFiniteSchur t e ht he = 1) :
    BoundedInverse (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude) where
  map := calibrationFullResolvent t e ht he J
  mem_domain := calibrationFullResolvent_mem_domain t e ht he J
  apply_map := calibrationFullResolvent_right t e ht he J hr
  map_apply u := by
    have hi : Function.Injective (calibrationFiniteSchur t e ht he) := by
      intro x y hxy
      have hleft (x : centralSpace) : J (calibrationFiniteSchur t e ht he x) = x :=
        congrArg (fun T : centralSpace →L[ℂ] centralSpace => T x) hl
      have hb := congrArg J hxy
      rwa [hleft,hleft] at hb
    have hinj := calibrationMaterial_injective_of_finite t e ht he hi
      (calibrationFullResolvent_right t e ht he J hr
        (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude u))
    exact congrArg Subtype.val hinj

def calibrationInverseFromSchur (hS : IsUnit (calibrationFiniteSchur t e ht he)) :
    BoundedInverse (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude) :=
  calibrationInverseFromFinite t e ht he (Ring.inverse (calibrationFiniteSchur t e ht he))
    (Ring.mul_inverse_cancel _ hS) (Ring.inverse_mul_cancel _ hS)

#print axioms calibrationInverseFromFinite
#print axioms calibrationFullResolvent_norm

end Maxwell.Continuum.Calibration
