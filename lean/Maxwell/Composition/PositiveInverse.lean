import Maxwell.Composition.PositiveEdges

/-! Full inverse and arbitrary-output residual transfer for the actual
positive-unit graph constructed from H. -/
noncomputable section
namespace Maxwell.Composition.PositiveEdges
open Matrix
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def operator (H : Matrix ι ι ℝ) :
    EuclideanSpace ℝ ((ι ⊕ ι) ⊕ Edge H) →L[ℝ] EuclideanSpace ℝ ((ι ⊕ ι) ⊕ Edge H) :=
  Matrix.toEuclideanCLM (n := (ι ⊕ ι) ⊕ Edge H) (𝕜 := ℝ) (matrix H)

def diagonalEquiv (H : Matrix ι ι ℝ) :
    EuclideanSpace ℝ (Edge H) ≃L[ℝ] EuclideanSpace ℝ (Edge H) :=
  ContinuousLinearEquiv.equivOfInverse'
    (Matrix.toEuclideanCLM (n := Edge H) (𝕜 := ℝ) (diagonalMatrix H))
    (Matrix.toEuclideanCLM (n := Edge H) (𝕜 := ℝ) (diagonalInverse H))
    (by
      change (Matrix.toEuclideanCLM (n := Edge H) (𝕜 := ℝ) (diagonalMatrix H)) *
        (Matrix.toEuclideanCLM (n := Edge H) (𝕜 := ℝ) (diagonalInverse H)) = 1
      rw [← map_mul, diagonal_mul_inverse, map_one])
    (by
      change (Matrix.toEuclideanCLM (n := Edge H) (𝕜 := ℝ) (diagonalInverse H)) *
        (Matrix.toEuclideanCLM (n := Edge H) (𝕜 := ℝ) (diagonalMatrix H)) = 1
      rw [← map_mul, inverse_mul_diagonal, map_one])

omit [DecidableEq ι] in
@[simp] theorem diagonalEquiv_coe (H : Matrix ι ι ℝ) :
    (diagonalEquiv H : EuclideanSpace ℝ (Edge H) →L[ℝ] EuclideanSpace ℝ (Edge H)) =
      Matrix.toEuclideanCLM (n := Edge H) (𝕜 := ℝ) (diagonalMatrix H) := rfl

omit [DecidableEq ι] in
@[simp] theorem diagonalEquiv_symm_coe (H : Matrix ι ι ℝ) :
    ((diagonalEquiv H).symm : EuclideanSpace ℝ (Edge H) →L[ℝ] EuclideanSpace ℝ (Edge H)) =
      Matrix.toEuclideanCLM (n := Edge H) (𝕜 := ℝ) (diagonalInverse H) := rfl

theorem upper_left (H : Matrix ι ι ℝ) :
    sumLeftProjection.comp ((operator H).comp sumLeftInjection) =
      Matrix.toEuclideanCLM (n := ι ⊕ ι) (𝕜 := ℝ) (Matrix.diagonal (endpointDiagonal H)) := by
  ext x i
  change (matrix H *ᵥ Sum.elim (WithLp.ofLp x) (0 : Edge H → ℝ)) (Sum.inl i) = _
  simp [matrix, Matrix.fromBlocks_mulVec]

theorem upper_right (H : Matrix ι ι ℝ) :
    sumLeftProjection.comp ((operator H).comp sumRightInjection) =
      Maxwell.rectangularEuclideanCLM (graph H).incidence := by
  ext x i
  change (matrix H *ᵥ Sum.elim (0 : ι ⊕ ι → ℝ) (WithLp.ofLp x)) (Sum.inl i) = ((graph H).incidence *ᵥ WithLp.ofLp x) i
  simp [matrix, Matrix.fromBlocks_mulVec]

theorem lower_left (H : Matrix ι ι ℝ) :
    sumRightProjection.comp ((operator H).comp sumLeftInjection) =
      Maxwell.rectangularEuclideanCLM (graph H).incidence.transpose := by
  ext x i
  change (matrix H *ᵥ Sum.elim (WithLp.ofLp x) (0 : Edge H → ℝ)) (Sum.inr i) = ((graph H).incidence.transpose *ᵥ WithLp.ofLp x) i
  simp [matrix, Matrix.fromBlocks_mulVec]

theorem lower_right (H : Matrix ι ι ℝ) :
    sumRightProjection.comp ((operator H).comp sumRightInjection) =
      Matrix.toEuclideanCLM (n := Edge H) (𝕜 := ℝ) (diagonalMatrix H) := by
  ext x i
  change (matrix H *ᵥ Sum.elim (0 : ι ⊕ ι → ℝ) (WithLp.ofLp x)) (Sum.inr i) = _
  simp [matrix, Matrix.fromBlocks_mulVec]

theorem operator_schur (H : Matrix ι ι ℝ) :
    brightSchurOperator (operator H) sumLeftInjection sumRightInjection
      sumLeftProjection sumRightProjection (diagonalEquiv H) =
      Matrix.toEuclideanCLM (n := ι ⊕ ι) (𝕜 := ℝ) (symmetricMatrix H) := by
  rw [brightSchurOperator, upper_left, upper_right, lower_left, diagonalEquiv_symm_coe]
  have hprod := rectangularEuclideanCLM_mul ((graph H).incidence * diagonalInverse H)
    (graph H).incidence.transpose
  conv_rhs at hprod => rw [rectangularEuclideanCLM_mul, rectangularEuclideanCLM_square,
    ContinuousLinearMap.comp_assoc]
  rw [← hprod, rectangularEuclideanCLM_square, ← map_sub, schur]

omit [DecidableEq ι] in
theorem inverse_diagonal_norm_le (H : Matrix ι ι ℝ) (habs : ∀ i j, |H i j| ≤ 1) :
    ‖((diagonalEquiv H).symm : EuclideanSpace ℝ (Edge H) →L[ℝ] EuclideanSpace ℝ (Edge H))‖ ≤ 1 := by
  rw [diagonalEquiv_symm_coe]
  apply Maxwell.matrix_toEuclideanCLM_norm_le _ 1 zero_le_one
  · intro e
    simpa [diagonalInverse, Matrix.diagonal_apply, apply_ite abs, weight] using habs e.val.1 e.val.2
  · intro e
    simpa [diagonalInverse, Matrix.diagonal_apply, apply_ite abs, weight] using habs e.val.1 e.val.2

theorem transpose_incidence_norm_le (H : Matrix ι ι ℝ)
    (hr : ∀ i, (rowSupport H i).card ≤ 3)
    (hc : ∀ j, (columnSupport H j).card ≤ 3) :
    ‖Maxwell.rectangularEuclideanCLM (graph H).incidence.transpose‖ ≤ Real.sqrt 6 := by
  have h := Maxwell.rectangularEuclideanCLM_norm_le_sqrt (graph H).incidence.transpose 2 3
    (by norm_num) (by norm_num)
    (fun e => ((graph H).incidence_column_sum e).le)
    (fun v => by simp only [Matrix.transpose_apply]; rw [(graph H).incidence_row_sum]; exact degree_le_three H hr hc v)
  norm_num at h ⊢
  exact h

theorem mixed_left_norm_le (H : Matrix ι ι ℝ) (habs : ∀ i j, |H i j| ≤ 1)
    (hr : ∀ i, (rowSupport H i).card ≤ 3)
    (hc : ∀ j, (columnSupport H j).card ≤ 3) :
    ‖((diagonalEquiv H).symm : EuclideanSpace ℝ (Edge H) →L[ℝ] EuclideanSpace ℝ (Edge H)).comp
      (sumRightProjection.comp ((operator H).comp sumLeftInjection))‖ ≤ Real.sqrt 6 := by
  rw [lower_left]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa only [one_mul] using (mul_le_mul (inverse_diagonal_norm_le H habs)
      (transpose_incidence_norm_le H hr hc) (norm_nonneg _) zero_le_one))

theorem mixed_right_norm_le (H : Matrix ι ι ℝ) (habs : ∀ i j, |H i j| ≤ 1)
    (hr : ∀ i, (rowSupport H i).card ≤ 3)
    (hc : ∀ j, (columnSupport H j).card ≤ 3) :
    ‖(sumLeftProjection.comp ((operator H).comp sumRightInjection)).comp
      ((diagonalEquiv H).symm : EuclideanSpace ℝ (Edge H) →L[ℝ] EuclideanSpace ℝ (Edge H))‖ ≤
      Real.sqrt 6 := by
  rw [upper_right]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa only [mul_one] using (mul_le_mul (incidence_norm_le H hr hc)
      (inverse_diagonal_norm_le H habs) (norm_nonneg _) (Real.sqrt_nonneg _)))

/-- The full positive graph is invertible; only the previously constructed
symmetric source block is an input equivalence. -/
def equiv (H : Matrix ι ι ℝ)
    (S : EuclideanSpace ℝ (ι ⊕ ι) ≃L[ℝ] EuclideanSpace ℝ (ι ⊕ ι))
    (hS : (S : EuclideanSpace ℝ (ι ⊕ ι) →L[ℝ] EuclideanSpace ℝ (ι ⊕ ι)) =
      Matrix.toEuclideanCLM (n := ι ⊕ ι) (𝕜 := ℝ) (symmetricMatrix H)) :
    EuclideanSpace ℝ ((ι ⊕ ι) ⊕ Edge H) ≃L[ℝ] EuclideanSpace ℝ ((ι ⊕ ι) ⊕ Edge H) :=
  complementaryEquiv (operator H) sumLeftInjection sumRightInjection
    sumLeftProjection sumRightProjection (diagonalEquiv H) S sumCoordinate_decomposition
    (fun c => congrArg (fun F => F c) (lower_right H))
    (by rw [operator_schur, hS])
    sumLeftProjection_left sumLeftProjection_right sumRightProjection_left sumRightProjection_right

@[simp] theorem equiv_coe (H : Matrix ι ι ℝ)
    (S : EuclideanSpace ℝ (ι ⊕ ι) ≃L[ℝ] EuclideanSpace ℝ (ι ⊕ ι))
    (hS : (S : EuclideanSpace ℝ (ι ⊕ ι) →L[ℝ] EuclideanSpace ℝ (ι ⊕ ι)) =
      Matrix.toEuclideanCLM (n := ι ⊕ ι) (𝕜 := ℝ) (symmetricMatrix H)) :
    (equiv H S hS : EuclideanSpace ℝ ((ι ⊕ ι) ⊕ Edge H) →L[ℝ]
      EuclideanSpace ℝ ((ι ⊕ ι) ⊕ Edge H)) = operator H := rfl

theorem inverse_norm_le (H : Matrix ι ι ℝ)
    (S : EuclideanSpace ℝ (ι ⊕ ι) ≃L[ℝ] EuclideanSpace ℝ (ι ⊕ ι))
    (hS : (S : EuclideanSpace ℝ (ι ⊕ ι) →L[ℝ] EuclideanSpace ℝ (ι ⊕ ι)) =
      Matrix.toEuclideanCLM (n := ι ⊕ ι) (𝕜 := ℝ) (symmetricMatrix H))
    (habs : ∀ i j, |H i j| ≤ 1)
    (hr : ∀ i, (rowSupport H i).card ≤ 3)
    (hc : ∀ j, (columnSupport H j).card ≤ 3)
    (Q : ℝ) (hQ : 1 ≤ Q)
    (hSnorm : ‖(S.symm : EuclideanSpace ℝ (ι ⊕ ι) →L[ℝ] EuclideanSpace ℝ (ι ⊕ ι))‖ ≤ Q) :
    ‖((equiv H S hS).symm : EuclideanSpace ℝ ((ι ⊕ ι) ⊕ Edge H) →L[ℝ]
      EuclideanSpace ℝ ((ι ⊕ ι) ⊕ Edge H))‖ ≤ 16 * Q := by
  have h := complementaryInverse_norm_le_of_local_bounds (operator H)
    sumLeftInjection sumRightInjection sumLeftProjection sumRightProjection (diagonalEquiv H) S
    (Real.sqrt 6) (Real.sqrt 6) sumLeftInjection_norm_le sumRightInjection_norm_le
    sumLeftProjection_norm_le sumRightProjection_norm_le
    (mixed_left_norm_le H habs hr hc) (mixed_right_norm_le H habs hr hc)
  change ‖complementaryInverse (operator H) sumLeftInjection sumRightInjection
    sumLeftProjection sumRightProjection (diagonalEquiv H) S‖ ≤ _
  have hcoef : (1 + Real.sqrt 6) * (1 + Real.sqrt 6) ≤ 13 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
    have hn := Real.sqrt_nonneg (6 : ℝ)
    have hu : Real.sqrt 6 ≤ (5 : ℝ) / 2 := by nlinarith
    nlinarith
  have hb := inverse_diagonal_norm_le H habs
  have hq0 : 0 ≤ Q := by linarith
  calc
    _ ≤ (1 + Real.sqrt 6) * (1 + Real.sqrt 6) *
        ‖(S.symm : EuclideanSpace ℝ (ι ⊕ ι) →L[ℝ] EuclideanSpace ℝ (ι ⊕ ι))‖ +
        ‖((diagonalEquiv H).symm : EuclideanSpace ℝ (Edge H) →L[ℝ] EuclideanSpace ℝ (Edge H))‖ := h
    _ ≤ 13 * Q + 1 := by gcongr
    _ ≤ 16 * Q := by linarith

/-- Errors in every mediator equation are retained by elimination. -/
theorem residual_transfer (H : Matrix ι ι ℝ) (habs : ∀ i j, |H i j| ≤ 1)
    (hr : ∀ i, (rowSupport H i).card ≤ 3)
    (hc : ∀ j, (columnSupport H j).card ≤ 3)
    (z : EuclideanSpace ℝ ((ι ⊕ ι) ⊕ Edge H)) (g : EuclideanSpace ℝ (ι ⊕ ι)) :
    ‖(Matrix.toEuclideanCLM (n := ι ⊕ ι) (𝕜 := ℝ) (symmetricMatrix H)) (sumLeftProjection z) - g‖ ≤
      4 * ‖operator H z - sumLeftInjection g‖ := by
  have hs : Real.sqrt 6 ≤ (3 : ℝ) := by
    have h := Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num)
    nlinarith [Real.sqrt_nonneg (6 : ℝ)]
  simpa using mediator_residual_transfer (operator H) sumLeftInjection sumRightInjection
    sumLeftProjection sumRightProjection (diagonalEquiv H)
    (Matrix.toEuclideanCLM (n := ι ⊕ ι) (𝕜 := ℝ) (symmetricMatrix H)) 1 zero_lt_one sumCoordinate_decomposition
    (fun c => congrArg (fun F => F c) (lower_right H))
    sumLeftProjection_left sumRightProjection_left
    (by simpa using operator_schur H)
    sumLeftProjection_norm_le sumRightProjection_norm_le
    ((mixed_right_norm_le H habs hr hc).trans hs) z g

end Maxwell.Composition.PositiveEdges
