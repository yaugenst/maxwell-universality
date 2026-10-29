import Maxwell.Composition.SubdivisionNorm
import Maxwell.Composition.SourceSubdivisionGraph

/-! Degree at most three for the actual routed matrix support, including
both original graph vertices and every internal path vertex. -/

noncomputable section
namespace Maxwell.Composition.SourceSubdivision

open Maxwell.Logical
open Maxwell.Logical.Routing
open scoped BigOperators

local instance (S : Source.SparseSystem) (precision : ℕ) :
    DecidableEq (SourceRouting.Vertex S precision) := Classical.decEq _
attribute [local instance] Classical.propDecidable

/-- Actual nonzero off-diagonal neighbors of a routed vertex. -/
def neighbors (S : Source.SparseSystem) (precision : ℕ)
    (a : SourceRouting.Vertex S precision) : Finset (SourceRouting.Vertex S precision) :=
  Finset.univ.filter fun b => b ≠ a ∧ matrix S precision a b ≠ 0

theorem offdiag_row_abs_sum_le_three (S : Source.SparseSystem) (precision : ℕ)
    (a : SourceRouting.Vertex S precision) :
    ∑ b : SourceRouting.Vertex S precision,
      (if b = a then 0 else |matrix S precision a b|) ≤ (3 : ℝ) := by
  cases a with
  | inl v =>
    exact (SubdivisionNorm.terminal_offdiag_row_abs_sum_le (SourceRouting.data S precision)
      (SourcePositive.graph S precision) (PositiveEdges.diagonal (SourcePositive.sourceH S precision)) v).trans
      (SourcePositive.degree_le_three S precision v)
  | inr i =>
    calc
      _ ≤ ∑ b : SourceRouting.Vertex S precision, |matrix S precision (Sum.inr i) b| := by
        apply Finset.sum_le_sum
        intro b _
        split_ifs
        · exact abs_nonneg _
        · exact le_rfl
      _ ≤ 3 := SubdivisionNorm.internal_row_abs_sum_le_three (SourceRouting.data S precision)
        (SourcePositive.graph S precision) (PositiveEdges.diagonal (SourcePositive.sourceH S precision)) i

/-- Positive unit off-diagonal entries identify support cardinality with
its absolute row sum, rather than bounding a separate supplied graph. -/
theorem neighbors_card_eq (S : Source.SparseSystem) (precision : ℕ)
    (a : SourceRouting.Vertex S precision) :
    ((neighbors S precision a).card : ℝ) =
      ∑ b : SourceRouting.Vertex S precision, if b = a then 0 else |matrix S precision a b| := by
  rw [neighbors, Finset.natCast_card_filter]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hba : b = a
  · subst b
    simp
  · by_cases hn : matrix S precision a b = 0
    · simp [hba, hn]
    · have h1 : matrix S precision a b = 1 :=
        (offdiagonal_zero_or_one S precision a b (Ne.symm hba)).resolve_left hn
      simp [hba, h1]

theorem degree_le_three (S : Source.SparseSystem) (precision : ℕ)
    (a : SourceRouting.Vertex S precision) : (neighbors S precision a).card ≤ 3 := by
  have h : ((neighbors S precision a).card : ℝ) ≤ 3 := by
    rw [neighbors_card_eq]
    exact offdiag_row_abs_sum_le_three S precision a
  exact_mod_cast h

theorem neighbors_local (S : Source.SparseSystem) (precision : ℕ)
    (a b : SourceRouting.Vertex S precision) (hb : b ∈ neighbors S precision a) :
    UnitAdjacent (SourceRouting.embedding S precision a) (SourceRouting.embedding S precision b) := by
  have h := (Finset.mem_filter.mp hb).2
  exact matrix_local S precision a b (Ne.symm h.1) h.2

end Maxwell.Composition.SourceSubdivision
