import Maxwell.Continuum.FiniteAuxiliaryLogical
import Maxwell.Composition.SourceMediator

/-! The complex continuum target inverse is supplied by the actual
sparse-source compiler and routed graph, with no discrete Maxwell input. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.FiniteAuxiliary

open Maxwell.Composition

variable (S : Source.SparseSystem) (precision : ℕ)
local instance sourceTargetDecidableEq : DecidableEq (SourceIncidence.V S precision) := Classical.decEq _

theorem exists_routed_target_equiv
    (hunit : IsUnit (Source.realMatrix S)) (hm : 2 ≤ S.nnz) (hp : 1 ≤ precision)
    (hsmall : ((S.nnz : ℝ)*Maxwell.condition₂ (Source.realMatrix S))*
      ((S.nnz : ℝ)/(2*2^precision)) ≤ 1/2)
    (κ K α : ℝ) (hκ : 1 ≤ κ) (hα : 0 < α)
    (hcondition : (S.nnz : ℝ)*Maxwell.condition₂ (Source.realMatrix S) ≤ κ)
    (hbudget : SourceMediator.inverseBudget S precision κ ≤ K)
    (β : Fin 3 → ℝ) (hβ : ∀ j, 3*α ≤ |β j|) :
    ∃ T : EuclideanSpace ℂ (SourceDecoration.Vertex S precision) ≃L[ℂ]
        EuclideanSpace ℂ (SourceDecoration.Vertex S precision),
      (T : EuclideanSpace ℂ (SourceDecoration.Vertex S precision) →L[ℂ]
        EuclideanSpace ℂ (SourceDecoration.Vertex S precision)) =
        logicalTarget (SourceIncidence.graph S precision) α
          (fun e => β (SourceIncidence.axis S precision e)) (SourceMediator.diagonal S precision) ∧
      ‖(T.symm : EuclideanSpace ℂ (SourceDecoration.Vertex S precision) →L[ℂ]
        EuclideanSpace ℂ (SourceDecoration.Vertex S precision))‖ ≤ 16*K/α := by
  obtain ⟨T, hT, hn⟩ := SourceMediator.exists_equiv S precision hunit hm hp hsmall κ α hκ hα hcondition
    (fun e => β (SourceIncidence.axis S precision e)) (fun e => hβ (SourceIncidence.axis S precision e))
  let Θ := (SourceIncidence.graph S precision).targetMatrix α
    (fun e => β (SourceIncidence.axis S precision e)) (SourceMediator.diagonal S precision)
  have hn' : ‖(T.symm : EuclideanSpace ℝ (SourceDecoration.Vertex S precision) →L[ℝ]
      EuclideanSpace ℝ (SourceDecoration.Vertex S precision))‖ ≤ 16*K/α :=
    hn.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbudget (by norm_num)) hα.le)
  have hA := inverseBound_of_real_equiv Θ T hT hn'
  exact ⟨ComplexInverse.complexEquiv Θ hA, rfl, ComplexInverse.complexEquiv_inverse_norm_le Θ hA⟩

#print axioms exists_routed_target_equiv

end Maxwell.Continuum.FiniteAuxiliary
