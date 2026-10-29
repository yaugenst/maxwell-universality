import Maxwell.Continuum.ClusterComplementFree

/-!
# Actual bounded material perturbation of the fixed complement

The potential is compressed by the literal fixed projection `Q`. The
Neumann inverse is constructed on the actual momentum-dependent maximal
domain and has norm at most two on the paper's complex box.
-/

noncomputable section

namespace Maxwell.Continuum.ClusterComplement

open FreeFiber SelfAdjointResolvent

def compressedMaterial : FiberSpace →L[ℂ] FiberSpace :=
  -(backgroundAmplitude : ℂ) • (complementProjection * potential * complementProjection)

theorem compressedMaterial_norm_le : ‖compressedMaterial‖ ≤ 7 * backgroundAmplitude := by
  have hprod : ‖complementProjection * potential * complementProjection‖ ≤ 7 := by
    calc
      ‖complementProjection * potential * complementProjection‖ ≤
          ‖complementProjection * potential‖ * ‖complementProjection‖ := norm_mul_le _ _
      _ ≤ (1 * 7) * 1 := mul_le_mul
        ((norm_mul_le _ _).trans (mul_le_mul complementProjection_norm_le potential_norm_le
          (norm_nonneg _) (by norm_num))) complementProjection_norm_le (norm_nonneg _) (by norm_num)
      _ = 7 := by norm_num
  rw [compressedMaterial, norm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos backgroundAmplitude_pos]
  nlinarith [mul_le_mul_of_nonneg_left hprod backgroundAmplitude_pos.le]

def regularizedMaterial (t : Momentum) (e : ℂ) : FiberSpace →ₗ.[ℂ] FiberSpace :=
  FormPerturbation.addBounded (regularizedFree t e) compressedMaterial

theorem regularizedMaterial_domain (t : Momentum) (e : ℂ) :
    (regularizedMaterial t e).domain = (operator (scaledMomentum t) (totalEnergy e)).domain :=
  regularizedFree_domain t e

theorem compressedMaterial_inverse_product_norm (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) :
    ‖compressedMaterial * (regularizedFreeInverse t e ht he).map‖ ≤ 1 / 4 := by
  have h := (norm_mul_le compressedMaterial (regularizedFreeInverse t e ht he).map).trans
    (mul_le_mul compressedMaterial_norm_le (regularizedFreeInverse_norm_le t e ht he)
      (norm_nonneg _) (mul_nonneg (by norm_num) backgroundAmplitude_pos.le))
  nlinarith [backgroundAmplitude_le]

def regularizedMaterialInverse (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) :
    BoundedInverse (regularizedMaterial t e) :=
  Neumann.perturbationInverse (regularizedFree t e) (regularizedFreeInverse t e ht he)
    compressedMaterial ((compressedMaterial_inverse_product_norm t e ht he).trans_lt (by norm_num))

theorem regularizedMaterialInverse_norm_le (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) :
    ‖(regularizedMaterialInverse t e ht he).map‖ ≤ 2 := by
  have hsmall := compressedMaterial_inverse_product_norm t e ht he
  have hden : 0 < 1 - ‖compressedMaterial * (regularizedFreeInverse t e ht he).map‖ := by linarith
  have hinv : (1 - ‖compressedMaterial * (regularizedFreeInverse t e ht he).map‖)⁻¹ ≤
      (4 / 3 : ℝ) := by
    have h := (inv_le_inv₀ hden (by norm_num : (0 : ℝ) < 3 / 4)).mpr (by linarith)
    norm_num at h
    exact h
  calc
    ‖(regularizedMaterialInverse t e ht he).map‖ ≤
        ‖(regularizedFreeInverse t e ht he).map‖ *
          (1 - ‖compressedMaterial * (regularizedFreeInverse t e ht he).map‖)⁻¹ :=
      Neumann.perturbationInverse_norm_le _ _ _ _
    _ ≤ (6 / 5 : ℝ) * (4 / 3) := mul_le_mul
      (regularizedFreeInverse_norm_le t e ht he) hinv (by positivity) (by norm_num)
    _ ≤ 2 := by norm_num

end Maxwell.Continuum.ClusterComplement
