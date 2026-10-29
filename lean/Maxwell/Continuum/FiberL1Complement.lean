import Maxwell.Continuum.FiberL1Space
import Maxwell.Continuum.ClusterComplementEquations

/-! The literal fixed cluster, its complete complement, and free/material
blocks act boundedly on the same absolutely summable alias coefficients. -/

noncomputable section
namespace Maxwell.Continuum.FiberL1

open FreeFiber ClusterComplement

set_option backward.isDefEq.respectTransparency false

def clusterProjection : Space →L[ℂ] Space :=
  blockMultiplier clusterBlock (by norm_num : (0 : ℝ) ≤ 1) clusterBlock_norm_le

def complementProjection : Space →L[ℂ] Space :=
  blockMultiplier complementBlock (by norm_num : (0 : ℝ) ≤ 1) complementBlock_norm_le

theorem clusterProjection_norm_le : ‖clusterProjection‖ ≤ 1 := blockMultiplier_norm_le _ _ _

theorem complementProjection_norm_le : ‖complementProjection‖ ≤ 1 := blockMultiplier_norm_le _ _ _

theorem inclusion_clusterProjection (u : Space) :
    inclusion (clusterProjection u) = ClusterComplement.clusterProjection (inclusion u) := rfl

theorem inclusion_complementProjection (u : Space) :
    inclusion (complementProjection u) = ClusterComplement.complementProjection (inclusion u) := by
  apply Subtype.ext
  funext ν
  rfl

def freeInverse (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) : Space →L[ℂ] Space :=
  blockMultiplier (regularizedInverseBlock t e) (by norm_num : (0 : ℝ) ≤ 6 / 5)
    (regularizedInverseBlock_norm_le t e ht he)

theorem freeInverse_norm_le (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) :
    ‖freeInverse t e ht he‖ ≤ 6 / 5 := blockMultiplier_norm_le _ _ _

theorem inclusion_freeInverse (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) (u : Space) :
    inclusion (freeInverse t e ht he u) = (regularizedFreeInverse t e ht he).map (inclusion u) := rfl

def materialPart : Space →L[ℂ] Space :=
  -(backgroundAmplitude : ℂ) • (complementProjection * potential * complementProjection)

theorem materialPart_norm_le : ‖materialPart‖ ≤ 7 * backgroundAmplitude := by
  have hprod : ‖complementProjection * potential * complementProjection‖ ≤ 7 := by
    calc
      ‖complementProjection * potential * complementProjection‖ ≤
          ‖complementProjection * potential‖ * ‖complementProjection‖ := norm_mul_le _ _
      _ ≤ (1 * 7) * 1 := mul_le_mul
        ((norm_mul_le _ _).trans (mul_le_mul complementProjection_norm_le potential_norm_le
          (norm_nonneg _) (by norm_num))) complementProjection_norm_le (norm_nonneg _) (by norm_num)
      _ = 7 := by norm_num
  rw [materialPart, norm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos backgroundAmplitude_pos]
  nlinarith [mul_le_mul_of_nonneg_left hprod backgroundAmplitude_pos.le]

theorem inclusion_materialPart (u : Space) :
    inclusion (materialPart u) = compressedMaterial (inclusion u) := by
  change inclusion (-(backgroundAmplitude : ℂ) •
    complementProjection (potential (complementProjection u))) =
    -(backgroundAmplitude : ℂ) • ClusterComplement.complementProjection
      (FreeFiber.potential (ClusterComplement.complementProjection (inclusion u)))
  rw [map_smul, inclusion_complementProjection, inclusion_potential, inclusion_complementProjection]

theorem materialPart_inverse_product_norm (t : Momentum) (e : ℂ)
    (ht : ∀ j, ‖t j‖ ≤ ((2 : ℝ) ^ 12)⁻¹) (he : ‖e‖ ≤ 8) :
    ‖materialPart * freeInverse t e ht he‖ ≤ 1 / 4 := by
  have h := (norm_mul_le materialPart (freeInverse t e ht he)).trans
    (mul_le_mul materialPart_norm_le (freeInverse_norm_le t e ht he)
      (norm_nonneg _) (mul_nonneg (by norm_num) backgroundAmplitude_pos.le))
  nlinarith [backgroundAmplitude_le]

#print axioms inclusion_materialPart
#print axioms materialPart_inverse_product_norm

end Maxwell.Continuum.FiberL1
