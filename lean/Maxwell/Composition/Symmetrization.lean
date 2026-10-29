import Maxwell.Composition.PositiveEdges
import Maxwell.Composition.SumCoordinates

/-! Exact Euclidean symmetrization of an arbitrary real square matrix.
The inverse is constructed from the original inverse and its adjoint;
neither symmetry of the original matrix nor a doubled norm bound is needed. -/

noncomputable section

namespace Maxwell.Composition.Symmetrization

open Matrix

variable {ι : Type*} [Fintype ι]

def offDiagonal (A B : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ (ι ⊕ ι) →L[ℝ] EuclideanSpace ℝ (ι ⊕ ι) :=
  sumLeftInjection.comp (A.comp sumRightProjection) +
    sumRightInjection.comp (B.comp sumLeftProjection)

@[simp] theorem offDiagonal_left
    (A B : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ (ι ⊕ ι)) :
    sumLeftProjection (offDiagonal A B x) = A (sumRightProjection x) := by
  simp [offDiagonal]

@[simp] theorem offDiagonal_right
    (A B : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ (ι ⊕ ι)) :
    sumRightProjection (offDiagonal A B x) = B (sumLeftProjection x) := by
  simp [offDiagonal]

theorem offDiagonal_norm_le
    (A B : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (C : ℝ) (hC : 0 ≤ C) (hA : ‖A‖ ≤ C) (hB : ‖B‖ ≤ C) :
    ‖offDiagonal A B‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  have ha : ‖A (sumRightProjection x)‖ ≤ C * ‖sumRightProjection x‖ :=
    (A.le_opNorm _).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have hb : ‖B (sumLeftProjection x)‖ ≤ C * ‖sumLeftProjection x‖ :=
    (B.le_opNorm _).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _))
  have hasq := pow_le_pow_left₀ (norm_nonneg _) ha 2
  have hbsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hx := sumCoordinate_norm_sq x
  have hy := sumCoordinate_norm_sq (offDiagonal A B x)
  simp only [offDiagonal_left, offDiagonal_right] at hy
  have hs : ‖offDiagonal A B x‖ ^ 2 ≤ (C * ‖x‖) ^ 2 := by
    nlinarith only [hasq, hbsq, hy, congrArg (fun t : ℝ => C ^ 2 * t) hx]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp hs

private theorem offDiagonal_inverse
    (A B C D : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (hAD : A.comp D = ContinuousLinearMap.id ℝ _)
    (hBC : B.comp C = ContinuousLinearMap.id ℝ _) :
    (offDiagonal A B).comp (offDiagonal C D) = ContinuousLinearMap.id ℝ _ := by
  apply ContinuousLinearMap.ext
  intro x
  have hl : A (D (sumLeftProjection x)) = sumLeftProjection x :=
    DFunLike.congr_fun hAD _
  have hr : B (C (sumRightProjection x)) = sumRightProjection x :=
    DFunLike.congr_fun hBC _
  rw [sumCoordinate_decomposition ((offDiagonal A B).comp (offDiagonal C D) x)]
  simpa only [ContinuousLinearMap.comp_apply, offDiagonal_left, offDiagonal_right,
    hl, hr, ContinuousLinearMap.id_apply] using (sumCoordinate_decomposition x).symm

/-- The actual block operator `(x,y) ↦ (e y,e† x)`, with inverse
`(x,y) ↦ ((e⁻¹)† y,e⁻¹ x)`. -/
def equiv (e : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ (ι ⊕ ι) ≃L[ℝ] EuclideanSpace ℝ (ι ⊕ ι) :=
  ContinuousLinearEquiv.equivOfInverse'
    (offDiagonal (e : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
      (e : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι).adjoint)
    (offDiagonal (e.symm : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι).adjoint
      (e.symm : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι))
    (offDiagonal_inverse _ _ _ _ (by simp) (by
      simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using
        congrArg ContinuousLinearMap.adjoint e.coe_symm_comp_coe))
    (offDiagonal_inverse _ _ _ _ (by
      simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using
        congrArg ContinuousLinearMap.adjoint e.coe_comp_coe_symm) (by simp))

theorem norm_le (e : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι) :
    ‖(equiv e : EuclideanSpace ℝ (ι ⊕ ι) →L[ℝ] EuclideanSpace ℝ (ι ⊕ ι))‖ ≤
      ‖(e : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)‖ := by
  apply offDiagonal_norm_le _ _ _ (norm_nonneg _) le_rfl
  exact le_of_eq (ContinuousLinearMap.adjoint.norm_map _)

theorem inverse_norm_le (e : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι) :
    ‖((equiv e).symm : EuclideanSpace ℝ (ι ⊕ ι) →L[ℝ]
      EuclideanSpace ℝ (ι ⊕ ι))‖ ≤
      ‖(e.symm : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)‖ := by
  apply offDiagonal_norm_le _ _ _ (norm_nonneg _)
  · exact le_of_eq (ContinuousLinearMap.adjoint.norm_map _)
  · exact le_rfl

variable [DecidableEq ι]

def operator (H : Matrix ι ι ℝ) :
    EuclideanSpace ℝ (ι ⊕ ι) →L[ℝ] EuclideanSpace ℝ (ι ⊕ ι) :=
  Matrix.toEuclideanCLM (n := ι ⊕ ι) (𝕜 := ℝ) (PositiveEdges.symmetricMatrix H)

theorem transpose_eq_adjoint (H : Matrix ι ι ℝ) :
    Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) H.transpose =
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) H).adjoint := by
  simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    ContinuousLinearMap.star_eq_adjoint] using
    (map_star (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) H)

theorem operator_eq (H : Matrix ι ι ℝ) :
    operator H = offDiagonal (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) H)
      (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) H).adjoint := by
  rw [← transpose_eq_adjoint]
  ext x i
  cases i with
  | inl i =>
    change (PositiveEdges.symmetricMatrix H *ᵥ WithLp.ofLp x) (Sum.inl i) =
      (H *ᵥ (fun j => x (Sum.inr j))) i + 0
    simp [PositiveEdges.symmetricMatrix, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type]
  | inr i =>
    change (PositiveEdges.symmetricMatrix H *ᵥ WithLp.ofLp x) (Sum.inr i) =
      0 + (H.transpose *ᵥ (fun j => x (Sum.inl j))) i
    simp [PositiveEdges.symmetricMatrix, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type]

theorem equiv_coe (H : Matrix ι ι ℝ)
    (e : EuclideanSpace ℝ ι ≃L[ℝ] EuclideanSpace ℝ ι)
    (he : (e : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) H) :
    (equiv e : EuclideanSpace ℝ (ι ⊕ ι) →L[ℝ] EuclideanSpace ℝ (ι ⊕ ι)) =
      operator H := by
  change offDiagonal _ _ = operator H
  rw [he, operator_eq]

theorem operator_norm_le (H : Matrix ι ι ℝ) :
    ‖operator H‖ ≤ ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) H‖ := by
  rw [operator_eq]
  apply offDiagonal_norm_le _ _ _ (norm_nonneg _) le_rfl
  exact le_of_eq (ContinuousLinearMap.adjoint.norm_map _)

/-- Selecting the right coordinates of an arbitrary proposed solution to the
symmetrized system recovers the original residual by an orthogonal projection. -/
theorem residual_projection (H : Matrix ι ι ℝ)
    (z : EuclideanSpace ℝ (ι ⊕ ι)) (g : EuclideanSpace ℝ ι) :
    sumLeftProjection (operator H z - sumLeftInjection g) =
      Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) H (sumRightProjection z) - g := by
  simp [operator_eq]

theorem residual_norm_le (H : Matrix ι ι ℝ)
    (z : EuclideanSpace ℝ (ι ⊕ ι)) (g : EuclideanSpace ℝ ι) :
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) H (sumRightProjection z) - g‖ ≤
      ‖operator H z - sumLeftInjection g‖ := by
  rw [← residual_projection]
  exact sumLeftProjection_norm_apply_le _

omit [DecidableEq ι] in
/-- The original input selector is literally the second copy of the coordinates. -/
theorem selected_coordinate (z : EuclideanSpace ℝ (ι ⊕ ι)) (i : ι) :
    sumRightProjection z i = z (Sum.inr i) := rfl

end Maxwell.Composition.Symmetrization
