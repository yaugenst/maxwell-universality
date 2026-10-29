import Maxwell.Composition.SourceDecoration

/-! The second (physical midpoint) Schur complement instantiated with the
actual routed sparse-source matrix and its proved inverse and degree bounds. -/
noncomputable section
namespace Maxwell.Composition.SourceMediator
open Maxwell.Logical
open scoped Matrix.Norms.L2Operator

variable (S : Source.SparseSystem) (precision : ℕ)
local instance : DecidableEq (SourceIncidence.V S precision) := Classical.decEq _

def diagonal (v : SourceIncidence.V S precision) : ℝ := SourceSubdivision.matrix S precision v v

def operator (α : ℝ) (β : SourceIncidence.E S precision → ℝ) :
    EuclideanSpace ℝ (SourceDecoration.Vertex S precision) →L[ℝ]
      EuclideanSpace ℝ (SourceDecoration.Vertex S precision) :=
  (SourceIncidence.graph S precision).targetOperator α β (diagonal S precision)

def source (α : ℝ) : EuclideanSpace ℝ (SourceDecoration.Vertex S precision) :=
  α • sumLeftInjection (SourceSubdivision.source S precision)

theorem logical_operator_eq :
    Matrix.toEuclideanCLM (n := SourceIncidence.V S precision) (𝕜 := ℝ)
      ((SourceIncidence.graph S precision).logicalMatrix (diagonal S precision)) =
      SourceSubdivision.operator S precision := by
  have h := SourceIncidence.logicalMatrix_eq S precision
  exact (congrArg (Matrix.toEuclideanCLM (n := SourceIncidence.V S precision) (𝕜 := ℝ)) h).trans
    (SourceSubdivision.operator_eq_matrix S precision).symm

def inverseBudget (L : ℝ) : ℝ :=
  9 * SourceSubdivision.ell S precision ^ 2 *
    (256 * L * ((sourceCircuit S precision).size : ℝ) ^ 4 + SourceSubdivision.ell S precision)

theorem inverseBudget_ge_one (L : ℝ) (hL : 1 ≤ L) : 1 ≤ inverseBudget S precision L := by
  have hell := SourceSubdivision.ell_ge_one S precision
  have hs := sq_nonneg (SourceSubdivision.ell S precision)
  have hc := pow_nonneg (show (0 : ℝ) ≤ (sourceCircuit S precision).size by positivity) 4
  have hterm : 0 ≤ 256 * L * ((sourceCircuit S precision).size : ℝ) ^ 4 := by positivity
  dsimp [inverseBudget]
  nlinarith

private theorem exists_equiv_from_routed
    (Γ : EuclideanSpace ℝ (SourceIncidence.V S precision) ≃L[ℝ]
      EuclideanSpace ℝ (SourceIncidence.V S precision))
    (hΓ : (Γ : EuclideanSpace ℝ (SourceIncidence.V S precision) →L[ℝ]
      EuclideanSpace ℝ (SourceIncidence.V S precision)) = SourceSubdivision.operator S precision)
    (K α : ℝ) (hK : 1 ≤ K) (hα : 0 < α)
    (hΓnorm : ‖(Γ.symm : EuclideanSpace ℝ (SourceIncidence.V S precision) →L[ℝ]
      EuclideanSpace ℝ (SourceIncidence.V S precision))‖ ≤ K)
    (β : SourceIncidence.E S precision → ℝ) (hβ : ∀ e, 3 * α ≤ |β e|) :
    ∃ T : EuclideanSpace ℝ (SourceDecoration.Vertex S precision) ≃L[ℝ]
        EuclideanSpace ℝ (SourceDecoration.Vertex S precision),
      (T : EuclideanSpace ℝ (SourceDecoration.Vertex S precision) →L[ℝ]
        EuclideanSpace ℝ (SourceDecoration.Vertex S precision)) = operator S precision α β ∧
      ‖(T.symm : EuclideanSpace ℝ (SourceDecoration.Vertex S precision) →L[ℝ]
        EuclideanSpace ℝ (SourceDecoration.Vertex S precision))‖ ≤ 16 * K / α := by
  exact (SourceIncidence.graph S precision).exists_target_equiv_paper_bound α K β
    (diagonal S precision) Γ hα hK hβ (SourceIncidence.degree_le_three S precision)
    (hΓ.trans (logical_operator_eq S precision).symm) hΓnorm

theorem exists_equiv (hunit : IsUnit (Source.realMatrix S)) (hm : 2 ≤ S.nnz)
    (hp : 1 ≤ precision)
    (hsmall : ((S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S)) *
      ((S.nnz : ℝ) / (2 * 2 ^ precision)) ≤ 1 / 2)
    (L α : ℝ) (hL : 1 ≤ L) (hα : 0 < α)
    (hcondition : (S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S) ≤ L)
    (β : SourceIncidence.E S precision → ℝ) (hβ : ∀ e, 3 * α ≤ |β e|) :
    ∃ T : EuclideanSpace ℝ (SourceDecoration.Vertex S precision) ≃L[ℝ]
        EuclideanSpace ℝ (SourceDecoration.Vertex S precision),
      (T : EuclideanSpace ℝ (SourceDecoration.Vertex S precision) →L[ℝ]
        EuclideanSpace ℝ (SourceDecoration.Vertex S precision)) = operator S precision α β ∧
      ‖(T.symm : EuclideanSpace ℝ (SourceDecoration.Vertex S precision) →L[ℝ]
        EuclideanSpace ℝ (SourceDecoration.Vertex S precision))‖ ≤ 16 * inverseBudget S precision L / α := by
  exact exists_equiv_from_routed S precision
    (SourceSubdivision.equiv S hunit hm precision hp hsmall)
    (SourceSubdivision.equiv_coe S hunit hm precision hp hsmall)
    (inverseBudget S precision L) α (inverseBudget_ge_one S precision L hL) hα
    (SourceSubdivision.inverse_norm_le S hunit hm precision hp hsmall L hL hcondition) β hβ

/-- All mediator equations may have residual; the original routed
residual follows for every supplied vector. -/
theorem routed_residual (α : ℝ) (β : SourceIncidence.E S precision → ℝ)
    (hα : 0 < α) (hβ : ∀ e, 3 * α ≤ |β e|)
    (z : EuclideanSpace ℝ (SourceDecoration.Vertex S precision)) :
    ‖SourceSubdivision.operator S precision (sumLeftProjection z) - SourceSubdivision.source S precision‖ ≤
      (4 / α) * ‖operator S precision α β z - source S precision α‖ := by
  have h := (SourceIncidence.graph S precision).target_residual_transfer α β (diagonal S precision)
    hα hβ (SourceIncidence.degree_le_three S precision) z (SourceSubdivision.source S precision)
  rw [logical_operator_eq] at h
  exact h

end Maxwell.Composition.SourceMediator
