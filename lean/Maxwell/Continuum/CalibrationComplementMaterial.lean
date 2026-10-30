import Maxwell.Continuum.CalibrationComplementFree

/-! Certified finite Neumann approximation of the manuscript's actual
24-central-alias complement. The tail bound is uniform over the whole
infinite fiber, including every longitudinal alias. -/

noncomputable section

namespace Maxwell.Continuum.Calibration

open FreeFiber SelfAdjointResolvent

def calibrationMaterialPerturbation : FiberSpace →L[ℂ] FiberSpace :=
  -(backgroundAmplitude : ℂ) • (noncentralAliasProjection*potential*noncentralAliasProjection)

theorem calibrationMaterialPerturbation_norm :
    ‖calibrationMaterialPerturbation‖ ≤ 7*backgroundAmplitude := by
  have hp : ‖noncentralAliasProjection*potential*noncentralAliasProjection‖ ≤ 7 := by
    calc
      _ ≤ ‖noncentralAliasProjection*potential‖*‖noncentralAliasProjection‖ := norm_mul_le _ _
      _ ≤ (1*7)*1 := mul_le_mul
        ((norm_mul_le _ _).trans (mul_le_mul noncentralAliasProjection_norm potential_norm_le
          (norm_nonneg _) zero_le_one)) noncentralAliasProjection_norm (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  rw [calibrationMaterialPerturbation, norm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos backgroundAmplitude_pos]
  exact (mul_le_mul_of_nonneg_left hp backgroundAmplitude_pos.le).trans_eq (mul_comm _ _)

def calibrationMaterial (t : Momentum) (e : ℂ) : FiberSpace →ₗ.[ℂ] FiberSpace :=
  FormPerturbation.addBounded (calibrationFree t e) calibrationMaterialPerturbation

theorem calibrationMaterial_domain (t : Momentum) (e : ℂ) :
    (calibrationMaterial t e).domain = (operator (scaledMomentum t) (totalEnergy e)).domain :=
  calibrationFree_domain t e

theorem calibration_ratio_le_half : 7*backgroundAmplitude ≤ 1/2 := by
  linarith [backgroundAmplitude_le]

theorem calibration_product_norm (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8) :
    ‖calibrationMaterialPerturbation*(calibrationFreeInverse t e ht he).map‖ ≤ 7*backgroundAmplitude := by
  exact (norm_mul_le _ _).trans ((mul_le_mul calibrationMaterialPerturbation_norm
    (calibrationFreeInverse_norm t e ht he) (norm_nonneg _)
    (mul_nonneg (by norm_num) backgroundAmplitude_pos.le)).trans_eq (mul_one _))

def calibrationMaterialInverse (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8) :
    BoundedInverse (calibrationMaterial t e) :=
  FreeFiber.Neumann.perturbationInverse (calibrationFree t e) (calibrationFreeInverse t e ht he)
    calibrationMaterialPerturbation
    ((calibration_product_norm t e ht he).trans_lt (calibration_ratio_le_half.trans_lt (by norm_num)))

def calibrationInverseApprox (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8) (K : ℕ) :
    FiberSpace →L[ℂ] FiberSpace :=
  Neumann.inverseApprox (calibrationFreeInverse t e ht he).map calibrationMaterialPerturbation K

theorem calibrationInverseApprox_error (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8) (K : ℕ) :
    ‖(calibrationMaterialInverse t e ht he).map-calibrationInverseApprox t e ht he K‖ ≤
      2*(7*backgroundAmplitude)^K := by
  have hr0 : 0 ≤ 7*backgroundAmplitude := mul_nonneg (by norm_num) backgroundAmplitude_pos.le
  have hr : 7*backgroundAmplitude < 1 := calibration_ratio_le_half.trans_lt (by norm_num)
  have hi : (1-7*backgroundAmplitude)⁻¹ ≤ (2 : ℝ) := by
    have hh := (inv_le_inv₀ (by linarith : 0 < 1-7*backgroundAmplitude)
      (by norm_num : (0 : ℝ) < 1/2)).mpr (by linarith [calibration_ratio_le_half])
    norm_num at hh
    exact hh
  have hb := Neumann.inverseApprox_error (calibrationFreeInverse t e ht he).map
    calibrationMaterialPerturbation hr0 hr (calibration_product_norm t e ht he) K
  change ‖(calibrationMaterialInverse t e ht he).map-calibrationInverseApprox t e ht he K‖ ≤ _ at hb
  apply hb.trans
  calc
    _ ≤ (1*(7*backgroundAmplitude)^K)*2 := mul_le_mul
      (mul_le_mul_of_nonneg_right (calibrationFreeInverse_norm t e ht he) (pow_nonneg hr0 K))
      hi (by positivity) (by positivity)
    _ = _ := by ring

theorem calibrationInverseApprox_error_dyadic (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ)^12)⁻¹) (he : ‖e‖ ≤ 8) (K : ℕ) :
    ‖(calibrationMaterialInverse t e ht he).map-calibrationInverseApprox t e ht he K‖ ≤
      2*(1/2 : ℝ)^K := by
  exact (calibrationInverseApprox_error t e ht he K).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀
      (mul_nonneg (by norm_num) backgroundAmplitude_pos.le) calibration_ratio_le_half K) (by norm_num))

#print axioms calibrationMaterial_domain
#print axioms calibrationMaterialInverse
#print axioms calibrationInverseApprox_error_dyadic

end Maxwell.Continuum.Calibration
