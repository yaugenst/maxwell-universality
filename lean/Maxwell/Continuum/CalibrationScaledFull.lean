import Maxwell.Continuum.CalibrationScaledSchur
import Maxwell.Continuum.CalibrationFullApprox

/-! Full-inverse approximation with rationally replaceable pi and energy.
The error is measured on the entire infinite fiber. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.Calibration

open FreeFiber SelfAdjointResolvent

def scaledLiftApprox (u F : ℝ) (r : Fin 3 → ℝ)
    (hr : ∀ j, |r j| ≤ 1/16) (hu : 3 ≤ u ∧ u ≤ 4) (hF : 7 ≤ F ∧ F ≤ 8) (K : ℕ) :
    FiberSpace →L[ℂ] FiberSpace :=
  centralAliasProjection-scaledComplementApprox u F r hr hu hF K*calibrationRightCoupling

def scaledSourceApprox (u F : ℝ) (r : Fin 3 → ℝ)
    (hr : ∀ j, |r j| ≤ 1/16) (hu : 3 ≤ u ∧ u ≤ 4) (hF : 7 ≤ F ∧ F ≤ 8) (K : ℕ) :
    FiberSpace →L[ℂ] FiberSpace :=
  1-calibrationLeftCoupling*scaledComplementApprox u F r hr hu hF K

def scaledFullApprox (u F : ℝ) (r : Fin 3 → ℝ)
    (hr : ∀ j, |r j| ≤ 1/16) (hu : 3 ≤ u ∧ u ≤ 4) (hF : 7 ≤ F ∧ F ≤ 8) (K : ℕ) :
    FiberSpace →L[ℂ] FiberSpace :=
  scaledComplementApprox u F r hr hu hF K+scaledLiftApprox u F r hr hu hF K*
    extendCentral (Ring.inverse (scaledFiniteSchurApprox u F r hr hu hF K))*
      scaledSourceApprox u F r hr hu hF K

theorem scaledComplementApprox_actual_error (t : Momentum) (e : ℂ) (E u F : ℝ) (r : Fin 3 → ℝ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8)
    (hr : ∀ j, |r j| ≤ 1/16) (hE : 7 ≤ E ∧ E ≤ 8)
    (hu : 3 ≤ u ∧ u ≤ 4) (hF : 7 ≤ F ∧ F ≤ 8)
    (hq : scaledMomentum t = realMomentum (fun j => Real.pi*r j)) (henergy : totalEnergy e = E) (K : ℕ) :
    ‖calibrationComplementInverse t e ht he-scaledComplementApprox u F r hr hu hF K‖ ≤
      2*(1/2 : ℝ)^K+32*(|Real.pi-u|+|E-F|) := by
  have hid : scaledComplementApprox Real.pi E r hr ⟨Real.pi_gt_three.le,Real.pi_lt_four.le⟩ hE K =
      calibrationComplementApprox t e ht he K := by
    unfold scaledComplementApprox calibrationComplementApprox
    rw [scaledFreeInverse_eq_calibration t e E r ht he hr hE hq henergy]
    rfl
  have hb := scaledComplementApprox_rounding Real.pi u E F r hr
    ⟨Real.pi_gt_three.le,Real.pi_lt_four.le⟩ hu hE hF K
  rw [hid] at hb
  have htri := (norm_sub_le_norm_sub_add_norm_sub (calibrationComplementInverse t e ht he)
    (calibrationComplementApprox t e ht he K) (scaledComplementApprox u F r hr hu hF K)).trans
      (add_le_add (calibrationComplementApprox_error t e ht he K) hb)
  exact htri.trans (by nlinarith [abs_nonneg (Real.pi-u),abs_nonneg (E-F)])

theorem scaledFullApprox_error (t : Momentum) (e : ℂ) (E u F : ℝ) (r : Fin 3 → ℝ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8)
    (hr : ∀ j, |r j| ≤ 1/16) (hE : 7 ≤ E ∧ E ≤ 8)
    (hu : 3 ≤ u ∧ u ≤ 4) (hF : 7 ≤ F ∧ F ≤ 8)
    (hq : scaledMomentum t = realMomentum (fun j => Real.pi*r j)) (henergy : totalEnergy e = E)
    (R : BoundedInverse (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude))
    {M δ : ℝ} (hM : 1 ≤ M) (hR : ‖R.map‖ ≤ M) (K : ℕ)
    (hδ : 2*(1/2 : ℝ)^K+32*(|Real.pi-u|+|E-F|) ≤ δ) (hsmall : M*δ ≤ 1/2) :
    IsUnit (scaledFiniteSchurApprox u F r hr hu hF K) ∧
      ‖R.map-scaledFullApprox u F r hr hu hF K‖ ≤ 32*M^2*δ := by
  have hC := (scaledComplementApprox_actual_error t e E u F r ht he hr hE hu hF hq henergy K).trans hδ
  have hS : ‖calibrationFiniteSchur t e ht he-scaledFiniteSchurApprox u F r hr hu hF K‖ ≤ δ := by
    have hs := (scaledSchurApprox_actual_error t e E u F r ht he hr hE hu hF hq henergy K).trans hδ
    apply ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg _).trans hs)
    intro v
    change ‖calibrationSchur t e ht he v.val-scaledSchurApprox u F r hr hu hF K v.val‖ ≤ _
    exact ((calibrationSchur t e ht he-scaledSchurApprox u F r hr hu hF K).le_opNorm v.val).trans
      (mul_le_mul_of_nonneg_right hs (norm_nonneg _))
  have hJ := (calibrationFiniteInverse_norm_le t e ht he R).trans hR
  have hi := inverse_perturbation_estimate _ _ (calibrationFiniteSchur_isUnit_of_inverse t e ht he R)
    hJ hS hsmall
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hC
  have hδ1 : δ ≤ 1 := by nlinarith
  have hl : ‖calibrationLeftCoupling‖ ≤ 1 :=
    calibrationLeftCoupling_norm.trans (calibration_ratio_le_half.trans (by norm_num))
  have hright : ‖calibrationRightCoupling‖ ≤ 1 :=
    calibrationRightCoupling_norm.trans (calibration_ratio_le_half.trans (by norm_num))
  have hL : ‖calibrationLift t e ht he-scaledLiftApprox u F r hr hu hF K‖ ≤ δ := by
    have hid : calibrationLift t e ht he-scaledLiftApprox u F r hr hu hF K =
        -((calibrationComplementInverse t e ht he-scaledComplementApprox u F r hr hu hF K)*
          calibrationRightCoupling) := by
      unfold calibrationLift scaledLiftApprox
      rw [sub_mul,neg_sub]
      abel
    rw [hid,norm_neg]
    exact (norm_mul_le _ _).trans ((mul_le_mul hC hright (norm_nonneg _) hδ0).trans_eq (mul_one _))
  have hX : ‖calibrationSourceFactor t e ht he-scaledSourceApprox u F r hr hu hF K‖ ≤ δ := by
    have hid : calibrationSourceFactor t e ht he-scaledSourceApprox u F r hr hu hF K =
        -(calibrationLeftCoupling*(calibrationComplementInverse t e ht he-
          scaledComplementApprox u F r hr hu hF K)) := by
      unfold calibrationSourceFactor scaledSourceApprox
      rw [mul_sub,neg_sub]
      abel
    rw [hid,norm_neg]
    exact (norm_mul_le _ _).trans ((mul_le_mul hl hC (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hL' : ‖scaledLiftApprox u F r hr hu hF K‖ ≤ 3 := by
    have hb := norm_le_norm_sub_add (scaledLiftApprox u F r hr hu hF K) (calibrationLift t e ht he)
    rw [norm_sub_rev] at hb
    linarith [calibrationLift_norm t e ht he]
  have hJJ : ‖extendCentral (Ring.inverse (calibrationFiniteSchur t e ht he))-
      extendCentral (Ring.inverse (scaledFiniteSchurApprox u F r hr hu hF K))‖ ≤ 2*M^2*δ := by
    rw [← extendCentral_sub]
    exact (extendCentral_norm _).trans hi.2.2
  have hf := feshbach_inverse_difference
    (calibrationComplementInverse t e ht he) (scaledComplementApprox u F r hr hu hF K)
    (calibrationLift t e ht he) (scaledLiftApprox u F r hr hu hF K)
    (extendCentral (Ring.inverse (calibrationFiniteSchur t e ht he)))
    (extendCentral (Ring.inverse (scaledFiniteSchurApprox u F r hr hu hF K)))
    (calibrationSourceFactor t e ht he) (scaledSourceApprox u F r hr hu hF K)
    hM hδ0 hC hL hL' ((extendCentral_norm _).trans hJ)
    ((extendCentral_norm _).trans hi.2.1) hJJ (calibrationSourceFactor_norm t e ht he) hX
  refine ⟨hi.1,?_⟩
  have hformula : R.map = calibrationFullResolvent t e ht he
      (Ring.inverse (calibrationFiniteSchur t e ht he)) :=
    R.unique_map (calibrationInverseFromSchur t e ht he (calibrationFiniteSchur_isUnit_of_inverse t e ht he R))
  rw [hformula,calibrationFullResolvent_formula]
  exact hf

#print axioms scaledFullApprox_error

end Maxwell.Continuum.Calibration
