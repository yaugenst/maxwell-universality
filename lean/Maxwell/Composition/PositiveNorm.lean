import Maxwell.Composition.PositiveGraph
import Maxwell.SchurBound

/-! Symmetry and the dimension-independent Euclidean norm bound for the
actual positive-unit mediator matrix constructed from the circuit matrix. -/

noncomputable section

namespace Maxwell.Composition.PositiveEdges

open Matrix
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_isSymm (H : Matrix ι ι ℝ) : (matrix H).IsSymm := by
  show (matrix H).transpose = matrix H
  simp [matrix, diagonalMatrix, Matrix.fromBlocks_transpose]

theorem terminal_row_abs_sum (H : Matrix ι ι ℝ) (v : ι ⊕ ι) :
    (∑ w, |matrix H (Sum.inl v) w|) =
      |endpointDiagonal H v| + (graph H).degree v := by
  rw [Fintype.sum_sum_type]
  simp only [matrix, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂]
  rw [(graph H).incidence_row_sum]
  congr 1
  simp [Matrix.diagonal_apply, apply_ite]

theorem mediator_row_abs_sum (H : Matrix ι ι ℝ) (e : Edge H) :
    (∑ w, |matrix H (Sum.inr e) w|) = 2 + |-(weight H e)⁻¹| := by
  rw [Fintype.sum_sum_type]
  simp only [matrix, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.transpose_apply]
  rw [(graph H).incidence_column_sum]
  congr 1
  simp [diagonalMatrix, Matrix.diagonal_apply, apply_ite]

omit [Fintype ι] [DecidableEq ι] in
theorem mediator_abs_le_two (H : Matrix ι ι ℝ) (h : Alphabet H) (e : Edge H) :
    |-(weight H e)⁻¹| ≤ 2 := by
  have hm := mediator_alphabet H h e
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hm | hm | hm | hm <;> rw [hm] <;> norm_num

theorem matrix_row_abs_sum_le_six (H : Matrix ι ι ℝ) (h : Alphabet H)
    (hr : ∀ i, (rowSupport H i).card ≤ 3)
    (hc : ∀ j, (columnSupport H j).card ≤ 3)
    (v : (ι ⊕ ι) ⊕ Edge H) : ∑ w, |matrix H v w| ≤ 6 := by
  cases v with
  | inl v =>
    rw [terminal_row_abs_sum]
    have hd := degree_le_three H hr hc v
    have he := endpoint_abs_le H (alphabet_abs_le H h) v
    linarith
  | inr e =>
    rw [mediator_row_abs_sum]
    have he := mediator_abs_le_two H h e
    linarith

/-- The actual positive-unit graph matrix has Euclidean operator norm at most
six, independently of the source dimension and number of allocated gates. -/
theorem matrix_norm_le_six (H : Matrix ι ι ℝ) (h : Alphabet H)
    (hr : ∀ i, (rowSupport H i).card ≤ 3)
    (hc : ∀ j, (columnSupport H j).card ≤ 3) :
    ‖Matrix.toEuclideanCLM (n := (ι ⊕ ι) ⊕ Edge H) (𝕜 := ℝ) (matrix H)‖ ≤ 6 := by
  exact Maxwell.symmetric_matrix_toEuclideanCLM_norm_le (matrix H) 6
    (by norm_num) (matrix_isSymm H) (matrix_row_abs_sum_le_six H h hr hc)

omit [Fintype ι] [DecidableEq ι] in
/-- Every actual positive edge joins a terminal to a mediator. -/
theorem positiveGraph_bipartite (H : Matrix ι ι ℝ) (e : Edge H ⊕ Edge H) :
    ∃ (v : ι ⊕ ι) (m : Edge H),
      (positiveGraph H).tail e = Sum.inl v ∧ (positiveGraph H).head e = Sum.inr m := by
  cases e with
  | inl e => exact ⟨Sum.inl e.val.1, e, rfl, rfl⟩
  | inr e => exact ⟨Sum.inr e.val.2, e, rfl, rfl⟩

end Maxwell.Composition.PositiveEdges
