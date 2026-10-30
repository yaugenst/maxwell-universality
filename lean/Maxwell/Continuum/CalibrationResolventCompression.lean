import Maxwell.Continuum.CalibrationResolvent

/-! The inverse of the actual 24-dimensional calibration Schur matrix
is the compression of the full Maxwell inverse. This supplies its norm
bound without a finite-matrix conditioning premise. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.Calibration

open FreeFiber SelfAdjointResolvent

variable (t : Momentum) (e : ℂ)
variable (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8)

def calibrationFiniteInverseOfFull
    (R : BoundedInverse (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude)) :
    centralSpace →L[ℂ] centralSpace :=
  centralProjectionToSpace.comp (R.map.comp centralSpace.subtypeL)

theorem calibrationFiniteInverseOfFull_left
    (R : BoundedInverse (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude)) :
    calibrationFiniteInverseOfFull t e R*calibrationFiniteSchur t e ht he = 1 := by
  apply ContinuousLinearMap.ext
  intro u
  change centralProjectionToSpace (R.map (calibrationFiniteSchur t e ht he u).val) = u
  rw [calibrationFiniteSchur_apply,← calibrationLift_residual t e ht he u.val]
  rw [R.map_apply]
  apply Subtype.ext
  exact (calibrationLift_central t e ht he u.val).trans
    ((mem_centralSpace_iff _).mp u.property)

theorem calibrationFiniteSchur_isUnit_of_inverse
    (R : BoundedInverse (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude)) :
    IsUnit (calibrationFiniteSchur t e ht he) := by
  have hl (u : centralSpace) : calibrationFiniteInverseOfFull t e R
      (calibrationFiniteSchur t e ht he u) = u :=
    congrArg (fun T : centralSpace →L[ℂ] centralSpace => T u)
      (calibrationFiniteInverseOfFull_left t e ht he R)
  have hinj : Function.Injective (calibrationFiniteSchur t e ht he).toLinearMap := by
    intro u v huv
    change calibrationFiniteSchur t e ht he u = calibrationFiniteSchur t e ht he v at huv
    have h := congrArg (calibrationFiniteInverseOfFull t e R) huv
    rwa [hl,hl] at h
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hinj,LinearMap.injective_iff_surjective.mp hinj⟩

theorem calibrationFiniteInverseOfFull_eq
    (R : BoundedInverse (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude)) :
    calibrationFiniteInverseOfFull t e R = Ring.inverse (calibrationFiniteSchur t e ht he) := by
  have hS := calibrationFiniteSchur_isUnit_of_inverse t e ht he R
  have hl := calibrationFiniteInverseOfFull_left t e ht he R
  calc
    _ = calibrationFiniteInverseOfFull t e R*
        (calibrationFiniteSchur t e ht he*Ring.inverse (calibrationFiniteSchur t e ht he)) := by
      rw [Ring.mul_inverse_cancel _ hS,mul_one]
    _ = _ := by rw [← mul_assoc,hl,one_mul]

theorem calibrationFiniteInverse_norm_le
    (R : BoundedInverse (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude)) :
    ‖Ring.inverse (calibrationFiniteSchur t e ht he)‖ ≤ ‖R.map‖ := by
  rw [← calibrationFiniteInverseOfFull_eq t e ht he R]
  calc
    _ ≤ ‖centralProjectionToSpace‖*(‖R.map‖*‖centralSpace.subtypeL‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1*(‖R.map‖*1) := by
      gcongr
      · exact centralProjectionToSpace_norm
      · exact centralSpace.norm_subtypeL_le
    _ = _ := by ring

theorem calibration_boundedInverse_iff :
    Nonempty (BoundedInverse (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude)) ↔
      IsUnit (calibrationFiniteSchur t e ht he) :=
  ⟨fun ⟨R⟩ => calibrationFiniteSchur_isUnit_of_inverse t e ht he R,
   fun hS => ⟨calibrationInverseFromSchur t e ht he hS⟩⟩

#print axioms calibrationFiniteInverse_norm_le
#print axioms calibration_boundedInverse_iff

end Maxwell.Continuum.Calibration
