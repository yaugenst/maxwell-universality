import Maxwell.Continuum.FiniteAuxiliarySourceEquation

/-! Quantitative bounds for the literal source-equation inverse. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary

attribute [local irreducible] Auxiliary.resolvent

variable {ι : Type*} [Fintype ι]

theorem sourceInverse_norm {h z σ B : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (r : ι → Space)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) h⁻¹) (Metric.ball (r j) h⁻¹))
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι) (hB : 0 ≤ B)
    (hA : ‖(A.symm : DefectSpace ι →L[ℂ] DefectSpace ι)‖ ≤ B) :
    ‖sourceInverse D hσ0 hσ r A‖ ≤ 1+4*B*(h^2)⁻¹ := by
  have hcomp : ‖(insertion h r).comp ((A.symm : DefectSpace ι →L[ℂ] DefectSpace ι).comp
      ((collection h r).comp (resolvent D hσ0 hσ)))‖ ≤ 1*(B*(1*(4*(h^2)⁻¹))) := by
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    apply mul_le_mul (insertion_norm D.h_pos r hdisj) _ (norm_nonneg _) zero_le_one
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    apply mul_le_mul hA _ (norm_nonneg _) hB
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    exact mul_le_mul (collection_norm D.h_pos r hdisj) (resolvent_norm_le D hσ0 hσ)
      (norm_nonneg _) zero_le_one
  unfold sourceInverse
  apply (norm_add_le _ _).trans
  have hone : ‖(1 : FieldL2 →L[ℂ] FieldL2)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  calc
    _ ≤ 1+1*(B*(1*(4*(h^2)⁻¹))) := add_le_add hone hcomp
    _ = _ := by ring

theorem sourceInverse_norm_length {L z σ K α : ℝ} (D : Calibration L⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ L⁻¹^4/64) (r : ι → Space)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) L) (Metric.ball (r j) L))
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι) (hK : 0 ≤ K) (hα : 0 < α)
    (hA : ‖(A.symm : DefectSpace ι →L[ℂ] DefectSpace ι)‖ ≤ 256*K/α) :
    ‖sourceInverse D hσ0 hσ r A‖ ≤ 1+1024*K*L^2/α := by
  have hs := sourceInverse_norm D hσ0 hσ r (by simpa only [inv_inv] using hdisj)
    A (show 0 ≤ 256*K/α by positivity) hA
  simp only [inv_pow, inv_inv] at hs
  convert hs using 1
  ring

#print axioms sourceInverse_norm_length

end Maxwell.Continuum.FiniteAuxiliary
