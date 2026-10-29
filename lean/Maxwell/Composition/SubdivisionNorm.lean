import Maxwell.Composition.SourceSubdivision

/-! Uniform Euclidean norm and row-degree bounds for the actual subdivision
matrix.  Internal path length does not enter these forward-operator bounds. -/

noncomputable section
namespace Maxwell.Composition.SubdivisionNorm

open Matrix
open Maxwell.Logical
open Maxwell.Logical.Routing
open scoped BigOperators

private theorem fin_indicator_sum_le_one (n k : ℕ) :
    (∑ j : Fin n, if j.val = k then (1 : ℝ) else 0) ≤ 1 := by
  by_cases hk : k < n
  · have he (j : Fin n) : j.val = k ↔ j = ⟨k, hk⟩ := by
      constructor
      · intro h; apply Fin.ext; exact h
      · exact congrArg Fin.val
    simp only [he]
    simp
  · have he (j : Fin n) : j.val ≠ k := by have := j.isLt; omega
    simp only [he, ↓reduceIte, Finset.sum_const_zero]
    norm_num

variable {V E : Type*} {half : ℕ} (data : Gluing.Data V E half)

theorem pathMatrix_row_abs_sum_le_two (e : E)
    (i : Fin ((EdgeWalk.edgeWalk data e).length - 1)) :
    ∑ j, |SubdivisionSchur.pathMatrix data e i j| ≤ (2 : ℝ) := by
  have hentry (j : Fin ((EdgeWalk.edgeWalk data e).length - 1)) :
      |SubdivisionSchur.pathMatrix data e i j| ≤
        (if j.val = i.val + 1 then (1 : ℝ) else 0) +
        (if j.val = i.val - 1 then (1 : ℝ) else 0) := by
    rw [SubdivisionSchur.pathMatrix_consecutive]
    split_ifs <;> norm_num at *
    omega
  calc
    _ ≤ ∑ j : Fin ((EdgeWalk.edgeWalk data e).length - 1),
        ((if j.val = i.val + 1 then (1 : ℝ) else 0) +
          (if j.val = i.val - 1 then (1 : ℝ) else 0)) :=
      Finset.sum_le_sum (fun j _ => hentry j)
    _ = (∑ j : Fin ((EdgeWalk.edgeWalk data e).length - 1),
        if j.val = i.val + 1 then (1 : ℝ) else 0) +
        ∑ j : Fin ((EdgeWalk.edgeWalk data e).length - 1),
          if j.val = i.val - 1 then (1 : ℝ) else 0 := Finset.sum_add_distrib
    _ ≤ 1 + 1 := add_le_add (fin_indicator_sum_le_one _ _) (fin_indicator_sum_le_one _ _)
    _ = 2 := by norm_num

theorem pathMatrix_symmetric (e : E)
    (i j : Fin ((EdgeWalk.edgeWalk data e).length - 1)) :
    SubdivisionSchur.pathMatrix data e i j = SubdivisionSchur.pathMatrix data e j i := by
  simp only [SubdivisionSchur.pathMatrix_consecutive, or_comm]

variable [Fintype E] [DecidableEq E]

omit [Fintype E] in
theorem internalMatrix_symmetric (i j : SubdivisionSchur.Internal data) :
    SubdivisionSchur.internalMatrix data i j = SubdivisionSchur.internalMatrix data j i := by
  rcases i with ⟨e, i⟩
  rcases j with ⟨f, j⟩
  by_cases he : e = f
  · subst f
    simp only [SubdivisionSchur.internalMatrix, Matrix.blockDiagonal'_apply_eq]
    exact pathMatrix_symmetric data e i j
  · rw [SubdivisionSchur.internalMatrix,
      Matrix.blockDiagonal'_apply_ne (SubdivisionSchur.pathMatrix data) i j he,
      Matrix.blockDiagonal'_apply_ne (SubdivisionSchur.pathMatrix data) j i (Ne.symm he)]

theorem internalMatrix_row_abs_sum_le_two (i : SubdivisionSchur.Internal data) :
    ∑ j, |SubdivisionSchur.internalMatrix data i j| ≤ (2 : ℝ) := by
  rcases i with ⟨e, i⟩
  rw [Fintype.sum_sigma, Finset.sum_eq_single e]
  · simpa only [SubdivisionSchur.internalMatrix, Matrix.blockDiagonal'_apply_eq] using
      pathMatrix_row_abs_sum_le_two data e i
  · intro f _ hfe
    apply Finset.sum_eq_zero
    intro j _
    rw [SubdivisionSchur.internalMatrix,
      Matrix.blockDiagonal'_apply_ne (SubdivisionSchur.pathMatrix data) i j (Ne.symm hfe), abs_zero]
  · simp

variable [Fintype V] [DecidableEq V]

local instance : DecidableEq (Subdivision.Vertex data) := Classical.decEq _
attribute [local instance] Classical.propDecidable

omit [Fintype E] [Fintype V] in
theorem matrix_symmetric (G : SignedIncidence V E) (diagonal : V → ℝ)
    (i j : Subdivision.Vertex data) :
    SubdivisionSchur.matrix data G diagonal i j = SubdivisionSchur.matrix data G diagonal j i := by
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      by_cases h : i = j
      · subst j; rfl
      · simp [SubdivisionSchur.matrix, h, Ne.symm h]
    | inr j => rfl
  | inr i =>
    cases j with
    | inl j => rfl
    | inr j => exact internalMatrix_symmetric data i j

theorem terminal_row_abs_sum_le (G : SignedIncidence V E) (diagonal : V → ℝ) (v : V) :
    ∑ w, |SubdivisionSchur.matrix data G diagonal (Sum.inl v) w| ≤
      |diagonal v| + G.degree v := by
  change (∑ w : V ⊕ SubdivisionSchur.Internal data,
    |Matrix.fromBlocks (Matrix.diagonal diagonal) (SubdivisionSchur.coupling data G)
      (SubdivisionSchur.coupling data G).transpose (SubdivisionSchur.internalMatrix data)
      (Sum.inl v) w|) ≤ _
  rw [Fintype.sum_sum_type]
  simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂]
  have hdiag : ∑ w : V, |(Matrix.diagonal diagonal) v w| = |diagonal v| := by
    simp [Matrix.diagonal_apply, apply_ite abs]
  rw [hdiag]
  exact add_le_add le_rfl (SubdivisionBlocks.coupling_row_abs_sum_le G
    (SubdivisionSchur.first data) (SubdivisionSchur.last data) v)

theorem terminal_offdiag_row_abs_sum_le (G : SignedIncidence V E) (diagonal : V → ℝ) (v : V) :
    ∑ w : Subdivision.Vertex data,
      (if w = Sum.inl v then 0 else |SubdivisionSchur.matrix data G diagonal (Sum.inl v) w|) ≤
      G.degree v := by
  change (∑ w : V ⊕ SubdivisionSchur.Internal data,
    @ite ℝ (w = Sum.inl v) (Classical.propDecidable _) 0
      |Matrix.fromBlocks (Matrix.diagonal diagonal) (SubdivisionSchur.coupling data G)
        (SubdivisionSchur.coupling data G).transpose (SubdivisionSchur.internalMatrix data)
        (Sum.inl v) w|) ≤ _
  rw [Fintype.sum_sum_type]
  simp only [Sum.inl.injEq, Sum.inr_ne_inl, ↓reduceIte,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂]
  have hdiag : ∑ w : V, (if w = v then 0 else |(Matrix.diagonal diagonal) v w|) = 0 := by
    apply Finset.sum_eq_zero
    intro w _
    by_cases h : w = v
    · simp only [h, ↓reduceIte]
    · simp [h, Ne.symm h]
  rw [hdiag, zero_add]
  exact SubdivisionBlocks.coupling_row_abs_sum_le G
    (SubdivisionSchur.first data) (SubdivisionSchur.last data) v

theorem internal_row_abs_sum_le_three (G : SignedIncidence V E) (diagonal : V → ℝ)
    (i : SubdivisionSchur.Internal data) :
    ∑ w, |SubdivisionSchur.matrix data G diagonal (Sum.inr i) w| ≤ (3 : ℝ) := by
  change (∑ w : V ⊕ SubdivisionSchur.Internal data,
    |Matrix.fromBlocks (Matrix.diagonal diagonal) (SubdivisionSchur.coupling data G)
      (SubdivisionSchur.coupling data G).transpose (SubdivisionSchur.internalMatrix data)
      (Sum.inr i) w|) ≤ _
  rw [Fintype.sum_sum_type]
  simp only [Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.transpose_apply]
  have hc := SubdivisionBlocks.coupling_col_abs_sum_le G
    (SubdivisionSchur.first data) (SubdivisionSchur.last data) (SubdivisionSchur.first_ne_last data) i
  have hp := internalMatrix_row_abs_sum_le_two data i
  exact (add_le_add hc hp).trans_eq (by norm_num)

theorem matrix_row_abs_sum_le_six (G : SignedIncidence V E) (diagonal : V → ℝ)
    (hdiagonal : ∀ v, |diagonal v| ≤ 3) (hdegree : ∀ v, G.degree v ≤ 3)
    (i : Subdivision.Vertex data) :
    ∑ j, |SubdivisionSchur.matrix data G diagonal i j| ≤ (6 : ℝ) := by
  cases i with
  | inl v =>
    exact (terminal_row_abs_sum_le data G diagonal v).trans
      ((add_le_add (hdiagonal v) (hdegree v)).trans_eq (by norm_num))
  | inr i => exact (internal_row_abs_sum_le_three data G diagonal i).trans (by norm_num)

theorem operator_norm_le_six (G : SignedIncidence V E) (diagonal : V → ℝ)
    (hdiagonal : ∀ v, |diagonal v| ≤ 3) (hdegree : ∀ v, G.degree v ≤ 3) :
    ‖SubdivisionSchur.operator data G diagonal‖ ≤ 6 := by
  apply Maxwell.matrix_toEuclideanCLM_norm_le (SubdivisionSchur.matrix data G diagonal) 6 (by norm_num)
  · exact matrix_row_abs_sum_le_six data G diagonal hdiagonal hdegree
  · intro j
    have h := matrix_row_abs_sum_le_six data G diagonal hdiagonal hdegree j
    simpa only [matrix_symmetric data G diagonal] using h

end Maxwell.Composition.SubdivisionNorm

namespace Maxwell.Composition.SourceSubdivision

open Maxwell.Logical

theorem matrix_symmetric (S : Source.SparseSystem) (precision : ℕ)
    (i j : SourceRouting.Vertex S precision) : matrix S precision i j = matrix S precision j i :=
  SubdivisionNorm.matrix_symmetric (SourceRouting.data S precision) (SourcePositive.graph S precision)
    (PositiveEdges.diagonal (SourcePositive.sourceH S precision)) i j

theorem operator_norm_le_six (S : Source.SparseSystem) (precision : ℕ) :
    ‖operator S precision‖ ≤ 6 :=
  SubdivisionNorm.operator_norm_le_six (SourceRouting.data S precision) (SourcePositive.graph S precision)
    (PositiveEdges.diagonal (SourcePositive.sourceH S precision))
    (PositiveEdges.diagonal_abs_le_three (SourcePositive.sourceH S precision)
      (SourcePositive.alphabet S precision) (SourcePositive.rowSupport_le_three S precision)
      (SourcePositive.columnSupport_le_three S precision))
    (SourcePositive.degree_le_three S precision)

end Maxwell.Composition.SourceSubdivision
