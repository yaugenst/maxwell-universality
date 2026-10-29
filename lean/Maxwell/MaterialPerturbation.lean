import Maxwell.Target
import Maxwell.SchurBound
import Maxwell.Perturbation

namespace Maxwell.Target

open scoped BigOperators

/-- The same four-cell averaging rule before rational coefficient emission. -/
noncomputable def realCellAverage (B : Box) (a : B.Cell → ℝ) (e : B.Edge) : ℝ :=
  (a (incidentCells e 0) + a (incidentCells e 1) +
    a (incidentCells e 2) + a (incidentCells e 3)) / 4

noncomputable def realCellOperator (B : Box) (a : B.Cell → ℝ) : Matrix B.Edge B.Edge ℝ :=
  (((curl B).transpose * curl B).map fun q => (q : ℝ)) -
    (1 / 64 : ℝ) • Matrix.diagonal (realCellAverage B a)

theorem realCellAverage_rational (B : Box) (a : B.Cell → ℚ) (e : B.Edge) :
    realCellAverage B (fun c => (a c : ℝ)) e = (edgeAverage a e : ℝ) := by
  simp [realCellAverage, edgeAverage]

/-- This real pre-rounding model is exactly the emitted rational operator
when the cells are rational; its curl is the actual relative-PEC incidence. -/
theorem realCellOperator_rational (B : Box) (a : B.Cell → ℚ) :
    realCellOperator B (fun c => (a c : ℝ)) =
      (operator B a).map fun q => (q : ℝ) := by
  ext e f
  by_cases h : e = f
  · subst f
    simp [realCellOperator, operator, realCellAverage_rational]
  · simp [realCellOperator, operator, h]

theorem realCellAverage_sub_bound (B : Box) (a b : B.Cell → ℝ)
    (δ : ℝ) (h : ∀ c, |a c - b c| ≤ δ) (e : B.Edge) :
    |realCellAverage B a e - realCellAverage B b e| ≤ δ := by
  have h0 := (abs_le.mp (h (incidentCells e 0)))
  have h1 := (abs_le.mp (h (incidentCells e 1)))
  have h2 := (abs_le.mp (h (incidentCells e 2)))
  have h3 := (abs_le.mp (h (incidentCells e 3)))
  apply abs_le.mpr
  dsimp [realCellAverage]
  constructor <;> linarith

theorem realCellOperator_sub_diagonal (B : Box) (a b : B.Cell → ℝ) :
    realCellOperator B a - realCellOperator B b =
      Matrix.diagonal (fun e => -(1 / 64 : ℝ) *
        (realCellAverage B a e - realCellAverage B b e)) := by
  ext e f
  by_cases h : e = f
  · subst f
    simp [realCellOperator]
    ring
  · simp [realCellOperator, h]

/-- Cell rounding has a dimension-independent full-operator norm cost.
All electric edges, including those adjacent to PEC, are covered. -/
theorem realCellOperator_sub_norm_le (B : Box) (a b : B.Cell → ℝ)
    (δ : ℝ) (hδ : 0 ≤ δ) (h : ∀ c, |a c - b c| ≤ δ) :
    ‖Matrix.toEuclideanCLM (n := B.Edge) (𝕜 := ℝ)
      (realCellOperator B a - realCellOperator B b)‖ ≤ δ / 64 := by
  rw [realCellOperator_sub_diagonal]
  apply Maxwell.matrix_toEuclideanCLM_norm_le _ _ (by positivity)
  · intro e
    simp only [Matrix.diagonal_apply]
    simp only [apply_ite abs, abs_zero]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [abs_mul]
    norm_num
    have he := realCellAverage_sub_bound B a b δ h e
    linarith
  · intro e
    simp only [Matrix.diagonal_apply]
    simp only [apply_ite abs, abs_zero]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [abs_mul]
    norm_num
    have he := realCellAverage_sub_bound B a b δ h e
    linarith

end Maxwell.Target
