import Maxwell.Continuum.CalibrationResolventCompression
import Maxwell.Continuum.CalibrationSchurApprox
import Maxwell.Continuum.CalibrationFeshbachEstimate

/-! A finite Neumann/Feshbach formula for the entire inverse. Its error
is measured on the full infinite fiber; the finite central inverse is
the only matrix inversion in the formula. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.Calibration

open FreeFiber SelfAdjointResolvent

def extendCentral (J : centralSpace →L[ℂ] centralSpace) : FiberSpace →L[ℂ] FiberSpace :=
  centralSpace.subtypeL.comp (J.comp centralProjectionToSpace)

theorem extendCentral_norm (J : centralSpace →L[ℂ] centralSpace) : ‖extendCentral J‖ ≤ ‖J‖ := by
  calc
    _ ≤ ‖centralSpace.subtypeL‖*(‖J‖*‖centralProjectionToSpace‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1*(‖J‖*1) := by
      gcongr
      · exact centralSpace.norm_subtypeL_le
      · exact centralProjectionToSpace_norm
    _ = _ := by ring

theorem extendCentral_sub (J K : centralSpace →L[ℂ] centralSpace) :
    extendCentral (J-K) = extendCentral J-extendCentral K := by
  apply ContinuousLinearMap.ext
  intro u
  rfl

variable (t : Momentum) (e : ℂ)
variable (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8)

def calibrationSourceFactor : FiberSpace →L[ℂ] FiberSpace :=
  1-calibrationLeftCoupling*calibrationComplementInverse t e ht he

def calibrationLiftApprox (K : ℕ) : FiberSpace →L[ℂ] FiberSpace :=
  centralAliasProjection-calibrationComplementApprox t e ht he K*calibrationRightCoupling

def calibrationSourceApprox (K : ℕ) : FiberSpace →L[ℂ] FiberSpace :=
  1-calibrationLeftCoupling*calibrationComplementApprox t e ht he K

def calibrationFullApprox (K : ℕ) : FiberSpace →L[ℂ] FiberSpace :=
  calibrationComplementApprox t e ht he K+
    calibrationLiftApprox t e ht he K*
      extendCentral (Ring.inverse (calibrationFiniteSchurApprox t e ht he K))*
        calibrationSourceApprox t e ht he K

theorem calibrationFullResolvent_formula (J : centralSpace →L[ℂ] centralSpace) :
    calibrationFullResolvent t e ht he J = calibrationComplementInverse t e ht he+
      calibrationLift t e ht he*extendCentral J*calibrationSourceFactor t e ht he := by
  apply ContinuousLinearMap.ext
  intro u
  rfl

theorem calibrationSourceFactor_norm : ‖calibrationSourceFactor t e ht he‖ ≤ 2 := by
  have hleft : ‖calibrationLeftCoupling‖ ≤ 1/2 :=
    calibrationLeftCoupling_norm.trans calibration_ratio_le_half
  apply (norm_sub_le _ _).trans
  apply (add_le_add ContinuousLinearMap.norm_id_le ((norm_mul_le _ _).trans
    (mul_le_mul hleft (calibrationComplementInverse_norm t e ht he)
      (norm_nonneg _) (by norm_num)))).trans
  norm_num

theorem calibrationLiftApprox_error (K : ℕ) :
    ‖calibrationLift t e ht he-calibrationLiftApprox t e ht he K‖ ≤ 2*(1/2 : ℝ)^K := by
  have hid : calibrationLift t e ht he-calibrationLiftApprox t e ht he K =
      -((calibrationComplementInverse t e ht he-calibrationComplementApprox t e ht he K)*
        calibrationRightCoupling) := by
    unfold calibrationLift calibrationLiftApprox
    rw [sub_mul,neg_sub]
    abel
  rw [hid,norm_neg]
  have hr : ‖calibrationRightCoupling‖ ≤ 1 :=
    calibrationRightCoupling_norm.trans (calibration_ratio_le_half.trans (by norm_num))
  exact (norm_mul_le _ _).trans ((mul_le_mul (calibrationComplementApprox_error t e ht he K)
    hr (norm_nonneg _) (by positivity)).trans_eq (mul_one _))

theorem calibrationSourceApprox_error (K : ℕ) :
    ‖calibrationSourceFactor t e ht he-calibrationSourceApprox t e ht he K‖ ≤ 2*(1/2 : ℝ)^K := by
  have hid : calibrationSourceFactor t e ht he-calibrationSourceApprox t e ht he K =
      -(calibrationLeftCoupling*(calibrationComplementInverse t e ht he-
        calibrationComplementApprox t e ht he K)) := by
    unfold calibrationSourceFactor calibrationSourceApprox
    rw [mul_sub,neg_sub]
    abel
  rw [hid,norm_neg]
  have hl : ‖calibrationLeftCoupling‖ ≤ 1 :=
    calibrationLeftCoupling_norm.trans (calibration_ratio_le_half.trans (by norm_num))
  exact (norm_mul_le _ _).trans ((mul_le_mul hl (calibrationComplementApprox_error t e ht he K)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul _))

theorem calibrationFullApprox_error
    (R : BoundedInverse (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude))
    {M : ℝ} (hM : 1 ≤ M) (hR : ‖R.map‖ ≤ M) (K : ℕ)
    (hK : M*(2*(1/2 : ℝ)^K) ≤ 1/2) :
    IsUnit (calibrationFiniteSchurApprox t e ht he K) ∧
      ‖R.map-calibrationFullApprox t e ht he K‖ ≤ 64*M^2*(1/2 : ℝ)^K := by
  have hS := calibrationFiniteSchur_isUnit_of_inverse t e ht he R
  have hJ := (calibrationFiniteInverse_norm_le t e ht he R).trans hR
  have hi := inverse_perturbation_estimate (calibrationFiniteSchur t e ht he)
    (calibrationFiniteSchurApprox t e ht he K) hS hJ
      (calibrationFiniteSchurApprox_error t e ht he K) hK
  have hδ0 : 0 ≤ 2*(1/2 : ℝ)^K := by positivity
  have hδ1 : 2*(1/2 : ℝ)^K ≤ 1 := by nlinarith
  have hL' : ‖calibrationLiftApprox t e ht he K‖ ≤ 3 := by
    have hb := norm_le_norm_sub_add (calibrationLiftApprox t e ht he K) (calibrationLift t e ht he)
    rw [norm_sub_rev] at hb
    linarith [calibrationLiftApprox_error t e ht he K,calibrationLift_norm t e ht he]
  have hJJ : ‖extendCentral (Ring.inverse (calibrationFiniteSchur t e ht he))-
      extendCentral (Ring.inverse (calibrationFiniteSchurApprox t e ht he K))‖ ≤
        2*M^2*(2*(1/2 : ℝ)^K) := by
    rw [← extendCentral_sub]
    exact (extendCentral_norm _).trans hi.2.2
  have hf := feshbach_inverse_difference
    (calibrationComplementInverse t e ht he) (calibrationComplementApprox t e ht he K)
    (calibrationLift t e ht he) (calibrationLiftApprox t e ht he K)
    (extendCentral (Ring.inverse (calibrationFiniteSchur t e ht he)))
    (extendCentral (Ring.inverse (calibrationFiniteSchurApprox t e ht he K)))
    (calibrationSourceFactor t e ht he) (calibrationSourceApprox t e ht he K) hM hδ0
    (calibrationComplementApprox_error t e ht he K) (calibrationLiftApprox_error t e ht he K) hL'
    ((extendCentral_norm _).trans hJ) ((extendCentral_norm _).trans hi.2.1) hJJ
    (calibrationSourceFactor_norm t e ht he) (calibrationSourceApprox_error t e ht he K)
  refine ⟨hi.1,?_⟩
  have hformula : R.map = calibrationFullResolvent t e ht he
      (Ring.inverse (calibrationFiniteSchur t e ht he)) :=
    R.unique_map (calibrationInverseFromSchur t e ht he hS)
  rw [hformula,calibrationFullResolvent_formula]
  exact hf.trans_eq (by ring)

#print axioms calibrationFullApprox_error

end Maxwell.Continuum.Calibration
