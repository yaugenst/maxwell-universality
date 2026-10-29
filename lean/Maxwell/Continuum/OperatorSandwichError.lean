import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Linarith

/-! Perturbing the two factors of a bounded quadratic operator. -/

noncomputable section

namespace Maxwell.Continuum.OperatorPerturbation

open scoped InnerProduct

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℂ E] [InnerProductSpace ℂ F] [CompleteSpace E] [CompleteSpace F]

theorem sandwich_difference_norm (A B : E →L[ℂ] F) (W : F →L[ℂ] F) :
    ‖A†.comp (W.comp A) - B†.comp (W.comp B)‖ ≤
      ‖A - B‖ * ‖W‖ * (‖A‖ + ‖B‖) := by
  have he : A†.comp (W.comp A) - B†.comp (W.comp B) =
      (A - B)†.comp (W.comp A) + B†.comp (W.comp (A - B)) := by
    simp only [map_sub, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]
    abel
  rw [he]
  calc
    _ ≤ ‖(A - B)†.comp (W.comp A)‖ + ‖B†.comp (W.comp (A - B))‖ := norm_add_le _ _
    _ ≤ ‖(A - B)†‖ * (‖W‖ * ‖A‖) + ‖B†‖ * (‖W‖ * ‖A - B‖) := by
      apply add_le_add
      · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
      · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ = _ := by rw [ContinuousLinearMap.adjoint.norm_map, ContinuousLinearMap.adjoint.norm_map]; ring

end Maxwell.Continuum.OperatorPerturbation
