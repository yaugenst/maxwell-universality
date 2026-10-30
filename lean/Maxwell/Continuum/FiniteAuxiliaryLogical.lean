import Maxwell.Composition.SignedMediator
import Maxwell.Composition.ComplexInverse

/-! The literal mediator target acts on complex bright coefficients with
the same inverse bound as the proved real incidence construction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

open Maxwell.Composition
open scoped Matrix.Norms.L2Operator

theorem inverseBound_of_real_equiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (T : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι)
    (hT : (T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) = Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A)
    {b : ℝ} (hb : ‖(T.symm : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)‖ ≤ b) :
    Probability.InverseBound A b := by
  let B := (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)).symm
    (T.symm : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
  have hB : Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) B =
      (T.symm : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :=
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)).apply_symm_apply _
  refine ⟨B, ?_, ?_, ?_⟩
  · apply (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)).injective
    rw [map_mul, map_one]
    change Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A *
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) B = 1
    rw [← hT, hB]
    apply ContinuousLinearMap.ext
    exact T.apply_symm_apply
  · apply (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)).injective
    rw [map_mul, map_one]
    change Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) B *
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A = 1
    rw [← hT, hB]
    apply ContinuousLinearMap.ext
    exact T.symm_apply_apply
  · change ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) B‖ ≤ b
    rw [hB]
    exact hb

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def logicalTarget (G : SignedIncidence V E) (α : ℝ) (β : E → ℝ) (diag : V → ℝ) :
    EuclideanSpace ℂ (V ⊕ E) →L[ℂ] EuclideanSpace ℂ (V ⊕ E) :=
  ComplexInverse.complexOperator (G.targetMatrix α β diag)

theorem exists_logicalTarget_equiv (G : SignedIncidence V E)
    (α K : ℝ) (β : E → ℝ) (diag : V → ℝ)
    (Γ : EuclideanSpace ℝ V ≃L[ℝ] EuclideanSpace ℝ V)
    (hα : 0 < α) (hK : 1 ≤ K) (hβ : ∀ e, 3*α ≤ |β e|)
    (hdeg : ∀ i, G.degree i ≤ 3)
    (hΓ : (Γ : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V) = Matrix.toEuclideanCLM (n := V) (𝕜 := ℝ) (G.logicalMatrix diag))
    (hΓnorm : ‖(Γ.symm : EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)‖ ≤ K) :
    ∃ T : EuclideanSpace ℂ (V ⊕ E) ≃L[ℂ] EuclideanSpace ℂ (V ⊕ E),
      (T : EuclideanSpace ℂ (V ⊕ E) →L[ℂ] EuclideanSpace ℂ (V ⊕ E)) = logicalTarget G α β diag ∧
      ‖(T.symm : EuclideanSpace ℂ (V ⊕ E) →L[ℂ] EuclideanSpace ℂ (V ⊕ E))‖ ≤ 16*K/α := by
  obtain ⟨T, hT, hn⟩ := G.exists_target_equiv_paper_bound α K β diag Γ hα hK hβ hdeg hΓ hΓnorm
  have hA := inverseBound_of_real_equiv (G.targetMatrix α β diag) T hT hn
  exact ⟨ComplexInverse.complexEquiv _ hA, rfl, ComplexInverse.complexEquiv_inverse_norm_le _ hA⟩

omit [Fintype V] in
theorem logicalTarget_matrix_schur (G : SignedIncidence V E)
    (α : ℝ) (β : E → ℝ) (diag : V → ℝ) (hβ : ∀ e, β e ≠ 0) :
    (G.terminalDiagonal α diag).map Complex.ofReal-
      (G.coupling β).map Complex.ofReal*
        (SignedIncidence.mediatorInverse α β).map Complex.ofReal*
          (G.coupling β).transpose.map Complex.ofReal =
      (α : ℂ) • (G.logicalMatrix diag).map Complex.ofReal := by
  have hp : (G.coupling β).map Complex.ofReal *
      (SignedIncidence.mediatorInverse α β).map Complex.ofReal *
      (G.coupling β).transpose.map Complex.ofReal =
      (G.coupling β * SignedIncidence.mediatorInverse α β * (G.coupling β).transpose).map Complex.ofReal := by
    change (G.coupling β).map Complex.ofRealHom *
      (SignedIncidence.mediatorInverse α β).map Complex.ofRealHom *
      (G.coupling β).transpose.map Complex.ofRealHom =
      (G.coupling β * SignedIncidence.mediatorInverse α β * (G.coupling β).transpose).map Complex.ofRealHom
    simp only [Matrix.map_mul]
  rw [hp]
  ext i j
  change ((G.terminalDiagonal α diag i j : ℝ) : ℂ)-
    (((G.coupling β * SignedIncidence.mediatorInverse α β * (G.coupling β).transpose) i j : ℝ) : ℂ) =
    (α : ℂ)*((G.logicalMatrix diag i j : ℝ) : ℂ)
  rw [← Complex.ofReal_sub, ← Complex.ofReal_mul]
  exact congrArg Complex.ofReal (congrFun (congrFun (G.target_schur α β diag hβ) i) j)

#print axioms exists_logicalTarget_equiv
#print axioms logicalTarget_matrix_schur

end Maxwell.Continuum.FiniteAuxiliary
