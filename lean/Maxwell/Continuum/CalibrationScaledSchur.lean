import Maxwell.Continuum.CalibrationScaledCentral
import Maxwell.Continuum.CalibrationNeumannRounding
import Maxwell.Continuum.CalibrationSchurApprox

/-! A literal finite-Neumann Schur operator with rationally replaceable
pi and total energy. The norm estimate is independent of the alias
radius and is compared to the actual infinite Maxwell Schur operator. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Calibration

open FreeFiber

def scaledCentralMaterial (t E : ℝ) (r : Fin 3 → ℝ)
    (hr : ∀ j, |r j| ≤ 1/16) (ht : 3 ≤ t ∧ t ≤ 4) (hE : 7 ≤ E ∧ E ≤ 8) : FiberSpace →L[ℂ] FiberSpace :=
  scaledCentralFree t E r hr ht hE-
    (backgroundAmplitude : ℂ) • (centralAliasProjection*potential*centralAliasProjection)

def scaledComplementApprox (t E : ℝ) (r : Fin 3 → ℝ)
    (hr : ∀ j, |r j| ≤ 1/16) (ht : 3 ≤ t ∧ t ≤ 4) (hE : 7 ≤ E ∧ E ≤ 8) (K : ℕ) : FiberSpace →L[ℂ] FiberSpace :=
  Neumann.inverseApprox (scaledFreeInverse t E r hr ht.1 hE) calibrationMaterialPerturbation K*
    noncentralAliasProjection

def scaledSchurApprox (t E : ℝ) (r : Fin 3 → ℝ)
    (hr : ∀ j, |r j| ≤ 1/16) (ht : 3 ≤ t ∧ t ≤ 4) (hE : 7 ≤ E ∧ E ≤ 8) (K : ℕ) : FiberSpace →L[ℂ] FiberSpace :=
  scaledCentralMaterial t E r hr ht hE-calibrationLeftCoupling*
    scaledComplementApprox t E r hr ht hE K*calibrationRightCoupling

theorem scaledSchurApprox_central (t E : ℝ) (r : Fin 3 → ℝ)
    (hr : ∀ j, |r j| ≤ 1/16) (ht : 3 ≤ t ∧ t ≤ 4) (hE : 7 ≤ E ∧ E ≤ 8) (K : ℕ) (v : FiberSpace) :
    centralAliasProjection (scaledSchurApprox t E r hr ht hE K v) = scaledSchurApprox t E r hr ht hE K v := by
  change centralAliasProjection ((scaledCentralFree t E r hr ht hE v-
    (backgroundAmplitude : ℂ) • centralAliasProjection (potential (centralAliasProjection v)))-
      calibrationLeftCoupling (scaledComplementApprox t E r hr ht hE K (calibrationRightCoupling v))) = _
  rw [map_sub, map_sub, map_smul, scaledCentralFree_central, centralAliasProjection_idempotent,
    calibrationLeftCoupling_central]
  rfl

def scaledFiniteSchurApprox (t E : ℝ) (r : Fin 3 → ℝ)
    (hr : ∀ j, |r j| ≤ 1/16) (ht : 3 ≤ t ∧ t ≤ 4) (hE : 7 ≤ E ∧ E ≤ 8) (K : ℕ) : centralSpace →L[ℂ] centralSpace :=
  restrictCentral (scaledSchurApprox t E r hr ht hE K) (scaledSchurApprox_central t E r hr ht hE K)

theorem scaledComplementApprox_rounding (t u E F : ℝ) (r : Fin 3 → ℝ)
    (hr : ∀ j, |r j| ≤ 1/16) (ht : 3 ≤ t ∧ t ≤ 4) (hu : 3 ≤ u ∧ u ≤ 4)
    (hE : 7 ≤ E ∧ E ≤ 8) (hF : 7 ≤ F ∧ F ≤ 8) (K : ℕ) :
    ‖scaledComplementApprox t E r hr ht hE K-scaledComplementApprox u F r hr hu hF K‖ ≤
      4*(2*|t-u|+|E-F|) := by
  unfold scaledComplementApprox
  rw [← sub_mul]
  have hN := Neumann.inverseApprox_rounding _ _ calibrationMaterialPerturbation
    (scaledFreeInverse_norm t E r hr ht.1 hE) (scaledFreeInverse_norm u F r hr hu.1 hF)
    (calibrationMaterialPerturbation_norm.trans calibration_ratio_le_half) K
  calc
    _ ≤ ‖Neumann.inverseApprox (scaledFreeInverse t E r hr ht.1 hE) calibrationMaterialPerturbation K-
      Neumann.inverseApprox (scaledFreeInverse u F r hr hu.1 hF) calibrationMaterialPerturbation K‖*
        ‖noncentralAliasProjection‖ := norm_mul_le _ _
    _ ≤ (4*(2*|t-u|+|E-F|))*1 := mul_le_mul
      (hN.trans (mul_le_mul_of_nonneg_left (scaledFreeInverse_rounding t u E F r hr ht hu hE hF) (by norm_num)))
      noncentralAliasProjection_norm (norm_nonneg _) (by positivity)
    _ = _ := mul_one _

theorem scaledSchurApprox_rounding (t u E F : ℝ) (r : Fin 3 → ℝ)
    (hr : ∀ j, |r j| ≤ 1/16) (ht : 3 ≤ t ∧ t ≤ 4) (hu : 3 ≤ u ∧ u ≤ 4)
    (hE : 7 ≤ E ∧ E ≤ 8) (hF : 7 ≤ F ∧ F ≤ 8) (K : ℕ) :
    ‖scaledSchurApprox t E r hr ht hE K-scaledSchurApprox u F r hr hu hF K‖ ≤
      32*(|t-u|+|E-F|) := by
  have hl : ‖calibrationLeftCoupling‖ ≤ 1 :=
    calibrationLeftCoupling_norm.trans (calibration_ratio_le_half.trans (by norm_num))
  have hright : ‖calibrationRightCoupling‖ ≤ 1 :=
    calibrationRightCoupling_norm.trans (calibration_ratio_le_half.trans (by norm_num))
  have hid : scaledSchurApprox t E r hr ht hE K-scaledSchurApprox u F r hr hu hF K =
      (scaledCentralFree t E r hr ht hE-scaledCentralFree u F r hr hu hF)-
        calibrationLeftCoupling*(scaledComplementApprox t E r hr ht hE K-
          scaledComplementApprox u F r hr hu hF K)*calibrationRightCoupling := by
    unfold scaledSchurApprox scaledCentralMaterial
    rw [mul_sub, sub_mul]
    abel
  rw [hid]
  calc
    _ ≤ ‖scaledCentralFree t E r hr ht hE-scaledCentralFree u F r hr hu hF‖+
      ‖calibrationLeftCoupling*(scaledComplementApprox t E r hr ht hE K-
          scaledComplementApprox u F r hr hu hF K)*calibrationRightCoupling‖ := norm_sub_le _ _
    _ ≤ (16*|t-u|+|E-F|)+1*(4*(2*|t-u|+|E-F|))*1 := add_le_add
      (scaledCentralFree_rounding t u E F r hr ht hu hE hF)
      ((norm_mul_le _ _).trans (mul_le_mul ((norm_mul_le _ _).trans
        (mul_le_mul hl (scaledComplementApprox_rounding t u E F r hr ht hu hE hF K)
          (norm_nonneg _) zero_le_one)) hright (norm_nonneg _) (by positivity)))
    _ ≤ _ := by nlinarith [abs_nonneg (t-u), abs_nonneg (E-F)]

theorem scaledSchurApprox_eq_calibration (t : Momentum) (e : ℂ) (E : ℝ) (r : Fin 3 → ℝ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8)
    (hr : ∀ j, |r j| ≤ 1/16) (hE : 7 ≤ E ∧ E ≤ 8)
    (hq : scaledMomentum t = realMomentum (fun j => Real.pi*r j)) (henergy : totalEnergy e = E) (K : ℕ) :
    scaledSchurApprox Real.pi E r hr ⟨Real.pi_gt_three.le, Real.pi_lt_four.le⟩ hE K =
      calibrationSchurApprox t e ht he K := by
  unfold scaledSchurApprox scaledCentralMaterial scaledComplementApprox
  rw [scaledCentralFree_eq_calibration t e E r hr hE hq henergy,
    scaledFreeInverse_eq_calibration t e E r ht he hr hE hq henergy]
  rfl

theorem scaledSchurApprox_actual_error (t : Momentum) (e : ℂ) (E u F : ℝ) (r : Fin 3 → ℝ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8)
    (hr : ∀ j, |r j| ≤ 1/16) (hE : 7 ≤ E ∧ E ≤ 8)
    (hu : 3 ≤ u ∧ u ≤ 4) (hF : 7 ≤ F ∧ F ≤ 8)
    (hq : scaledMomentum t = realMomentum (fun j => Real.pi*r j)) (henergy : totalEnergy e = E) (K : ℕ) :
    ‖calibrationSchur t e ht he-scaledSchurApprox u F r hr hu hF K‖ ≤
      2*(1/2 : ℝ)^K+32*(|Real.pi-u|+|E-F|) := by
  have h := scaledSchurApprox_rounding Real.pi u E F r hr
    ⟨Real.pi_gt_three.le, Real.pi_lt_four.le⟩ hu hE hF K
  rw [scaledSchurApprox_eq_calibration t e E r ht he hr hE hq henergy K] at h
  exact (norm_sub_le_norm_sub_add_norm_sub (calibrationSchur t e ht he)
    (calibrationSchurApprox t e ht he K) (scaledSchurApprox u F r hr hu hF K)).trans
      (add_le_add (calibrationSchurApprox_error t e ht he K) h)

#print axioms scaledSchurApprox_actual_error

end Maxwell.Continuum.Calibration
