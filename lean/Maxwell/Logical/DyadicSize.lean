import Maxwell.Logical.CopiedForest
import Maxwell.Logical.DyadicCompile

namespace Maxwell.Logical

theorem Horner.expression_leafCount {n : ℕ} (i : Fin n) (bits : List Bool) :
    (Horner.expression i bits).leafCount ≤ bits.length := by
  induction bits with
  | nil => simp [Horner.expression, Expression.leafCount]
  | cons b bits ih =>
      cases b <;> simp only [Horner.expression, Expression.leafCount, List.length_cons] <;> omega

theorem DyadicTerm.expression_leafCount {n : ℕ} (term : DyadicTerm n) :
    term.expression.leafCount ≤ term.bits.length := by
  cases hb : term.negative <;>
    simpa [DyadicTerm.expression, hb, Expression.leafCount] using
      Horner.expression_leafCount term.input term.bits

theorem rowExpression_leafCount {n : ℕ} (terms : List (DyadicTerm n)) (precision : ℕ)
    (h : ∀ term ∈ terms, term.bits.length ≤ precision) :
    (rowExpression terms).leafCount ≤ terms.length * precision := by
  induction terms with
  | nil => simp [rowExpression, Expression.leafCount]
  | cons term terms ih =>
      have ht := term.expression_leafCount.trans (h term (by simp))
      have hs := ih (fun t hm => h t (by simp [hm]))
      simp only [rowExpression, Expression.leafCount, List.length_cons]
      nlinarith

theorem dyadic_forest_leafCount {n : ℕ} (rows : List (List (DyadicTerm n))) (precision : ℕ)
    (h : ∀ row ∈ rows, ∀ term ∈ row, term.bits.length ≤ precision) :
    forestLeafCount (rows.map rowExpression) ≤ (rows.map List.length).sum * precision := by
  induction rows with
  | nil => simp [forestLeafCount]
  | cons row rows ih =>
      have hr := rowExpression_leafCount row precision (h row (by simp))
      have hs := ih (fun r hm => h r (by simp [hm]))
      simp only [List.map_cons, List.sum_cons, forestLeafCount]
      nlinarith

theorem dyadic_forest_gateCount {n : ℕ} (rows : List (List (DyadicTerm n))) (precision : ℕ)
    (h : ∀ row ∈ rows, ∀ term ∈ row, term.bits.length ≤ precision) :
    ((rows.map rowExpression).map Expression.gateCount).sum ≤
      (rows.map List.length).sum * (2 * precision + 3) + rows.length := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
      have hr := rowExpression_gateCount row precision (h row (by simp))
      have hs := ih (fun r hm => h r (by simp [hm]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith

/-- The complete executable copy-plus-row compiler satisfies the paper's
linear sparse-input gate bound, for all dimensions and precisions. -/
theorem dyadic_copied_forest_size {n : ℕ} (rows : List (List (DyadicTerm n)))
    (precision : ℕ) (hn : rows.length = n)
    (hm : n ≤ (rows.map List.length).sum)
    (h : ∀ row ∈ rows, ∀ term ∈ row, term.bits.length ≤ precision) :
    (compileCopiedForest (rows.map rowExpression)).size ≤
      6 * (rows.map List.length).sum * (precision + 1) := by
  rw [compileCopiedForest_size]
  have hl := dyadic_forest_leafCount rows precision h
  have hg := dyadic_forest_gateCount rows precision h
  rw [hn] at hg
  nlinarith

end Maxwell.Logical
