import Maxwell.Source
import Maxwell.Target
import Maxwell.TargetNorm
import Maxwell.Composition.WeightedWoodbury

-- The concrete retained-edge sum/product index needs a larger instance
-- synthesis expression budget; the checked propositions are unchanged.
set_option synthInstance.maxSize 1024

/-! Full-matrix conditioning in the exact `GoodDraw` matrix convention.
This converts an actually constructed continuous linear inverse to the
finite emitted Maxwell matrix's unit and Euclidean condition-number bounds. -/

noncomputable section

namespace Maxwell.Composition

section MatrixBinding

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_isUnit_of_operator_equiv (M : Matrix ι ι ℝ)
    (A : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι)
    (hA : (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) M) : IsUnit M := by
  apply (MulEquiv.isUnit_map (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι))).mp
  rw [← hA]
  exact ⟨A.toUnit, rfl⟩

theorem matrix_inverse_of_operator_equiv (M : Matrix ι ι ℝ)
    (A : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι)
    (hA : (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) M) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) M⁻¹ =
      (A.symm : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) := by
  have hu := matrix_isUnit_of_operator_equiv M A hA
  have hm : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M (M.isUnit_iff_isUnit_det.mp hu)
  have hop := congrArg (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι)) hm
  rw [map_mul, map_one, ← hA] at hop
  apply ContinuousLinearMap.ext
  intro x
  have hx := congrArg
    (fun T : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι => T (A.symm x)) hop
  simpa using hx

theorem matrix_condition_of_operator_equiv (M : Matrix ι ι ℝ)
    (A : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι)
    (hA : (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι) M)
    (J Q : ℝ) (hJ : 0 ≤ J)
    (hforward : ‖(A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)‖ ≤ J)
    (hinverse : ‖(A.symm : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)‖ ≤ Q) :
    condition₂ M ≤ J * Q := by
  rw [condition₂, matrix_inverse_of_operator_equiv M A hA, ← hA]
  exact mul_le_mul hforward hinverse (norm_nonneg _) hJ

end MatrixBinding

/-- The actual rational scalar-cell target always has operator norm at
most sixteen. Only its constructed inverse bound is needed here. -/
theorem target_full_conditioning {n : ℕ} (I : Target.Instance n)
    (A : EuclideanSpace ℝ I.box.Edge ≃L[ℝ] EuclideanSpace ℝ I.box.Edge)
    (hA : (A : EuclideanSpace ℝ I.box.Edge →L[ℝ] EuclideanSpace ℝ I.box.Edge) =
      I.realOperator)
    (Q : ℝ) (hQ : ‖(A.symm : EuclideanSpace ℝ I.box.Edge →L[ℝ]
      EuclideanSpace ℝ I.box.Edge)‖ ≤ Q) :
    IsUnit I.realMatrix ∧ condition₂ I.realMatrix ≤ 16 * Q := by
  constructor
  · exact matrix_isUnit_of_operator_equiv I.realMatrix A hA
  · apply matrix_condition_of_operator_equiv I.realMatrix A hA 16 Q (by norm_num) _ hQ
    rw [hA]
    exact Target.maxwell_real_toEuclideanCLM_norm_le I.material

/-- The weighted Birman--Schwinger core controls the condition number of
the actual complete emitted matrix, including every background and
complementary coordinate. The physical inverse is constructed by Woodbury. -/
theorem target_weighted_full_conditioning {D : Type*}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    {n : ℕ} (I : Target.Instance n)
    (K : EuclideanSpace ℝ I.box.Edge ≃L[ℝ] EuclideanSpace ℝ I.box.Edge)
    (V W M : D ≃L[ℝ] D)
    (Q : EuclideanSpace ℝ I.box.Edge →L[ℝ] D)
    (Qt : D →L[ℝ] EuclideanSpace ℝ I.box.Edge)
    (hphysical : I.realOperator = finitePhysicalOperator K V Q Qt)
    (hM : (M : D →L[ℝ] D) = weightedBirmanSchwinger K V W Q Qt)
    (L QM : ℝ) (hK : ‖(K.symm : EuclideanSpace ℝ I.box.Edge →L[ℝ]
      EuclideanSpace ℝ I.box.Edge)‖ ≤ L)
    (hW : ‖(W : D →L[ℝ] D)‖ ≤ 1) (hQ : ‖Q‖ ≤ 1) (hQt : ‖Qt‖ ≤ 1)
    (hcore : ‖(M.symm : D →L[ℝ] D)‖ ≤ QM) :
    IsUnit I.realMatrix ∧ condition₂ I.realMatrix ≤ 16 * (L + L ^ 2 * QM) := by
  have hop : (physicalEquivOfWeighted K V W M Q Qt hM :
      EuclideanSpace ℝ I.box.Edge →L[ℝ] EuclideanSpace ℝ I.box.Edge) =
      I.realOperator := (physicalEquivOfWeighted_operator K V W M Q Qt hM).trans
        hphysical.symm
  exact target_full_conditioning I (physicalEquivOfWeighted K V W M Q Qt hM) hop
    (L + L ^ 2 * QM)
    (physicalEquivOfWeighted_inverse_norm_le K V W M Q Qt hM L QM hK hW hQ hQt hcore)

end Maxwell.Composition
