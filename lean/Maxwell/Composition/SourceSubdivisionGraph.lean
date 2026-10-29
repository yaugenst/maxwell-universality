import Maxwell.Composition.SourceSubdivision
import Maxwell.Composition.SubdivisionLocality

/-! Locality and the finite matrix alphabet of the actual source-dependent
routed positive graph. All routing data come from the compiled source. -/

noncomputable section
namespace Maxwell.Composition.SourceSubdivision

open Maxwell.Logical
open Maxwell.Logical.Routing
open scoped BigOperators

local instance (S : Source.SparseSystem) (precision : ℕ) :
    DecidableEq (SourceRouting.Vertex S precision) := Classical.decEq _

theorem matrix_local (S : Source.SparseSystem) (precision : ℕ)
    (a b : SourceRouting.Vertex S precision) (hab : a ≠ b)
    (hnz : matrix S precision a b ≠ 0) :
    UnitAdjacent (SourceRouting.embedding S precision a)
      (SourceRouting.embedding S precision b) := by
  exact SubdivisionSchur.matrix_local (SourceRouting.data S precision)
    (SourcePositive.graph S precision) (PositiveEdges.diagonal (SourcePositive.sourceH S precision))
    (fun e => (SourceRouting.data_endpoint S precision e false).symm)
    (fun e => (SourceRouting.data_endpoint S precision e true).symm) a b hab hnz

theorem offdiagonal_zero_or_one (S : Source.SparseSystem) (precision : ℕ)
    (a b : SourceRouting.Vertex S precision) (hab : a ≠ b) :
    matrix S precision a b = 0 ∨ matrix S precision a b = 1 :=
  SubdivisionSchur.offdiagonal_zero_or_one (SourceRouting.data S precision)
    (SourcePositive.graph S precision) (PositiveEdges.diagonal (SourcePositive.sourceH S precision))
    (fun _ => rfl) a b hab

/-- The complete fixed diagonal alphabet, independent of source size,
precision, path length, or geometric placement. -/
def diagonalAlphabet : Finset ℝ :=
  (Finset.Icc (-6 : ℤ) 6).image (fun a : ℤ => (a : ℝ) / 2)

private theorem zero_mem_diagonalAlphabet : (0 : ℝ) ∈ diagonalAlphabet := by
  exact Finset.mem_image.mpr ⟨0, by norm_num, by norm_num⟩

theorem diagonal_alphabet (S : Source.SparseSystem) (precision : ℕ)
    (a : SourceRouting.Vertex S precision) : matrix S precision a a ∈ diagonalAlphabet := by
  cases a with
  | inl v =>
    simp only [matrix, SubdivisionSchur.matrix, Matrix.fromBlocks_apply₁₁,
      Matrix.diagonal_apply_eq]
    cases v with
    | inl v =>
      exact PositiveEdges.endpoint_alphabet (SourcePositive.sourceH S precision)
        (SourcePositive.alphabet S precision) (SourcePositive.rowSupport_le_three S precision)
        (SourcePositive.columnSupport_le_three S precision) v
    | inr e =>
      have h := PositiveEdges.mediator_alphabet (SourcePositive.sourceH S precision)
        (SourcePositive.alphabet S precision) e
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      change -(PositiveEdges.weight (SourcePositive.sourceH S precision) e)⁻¹ ∈ diagonalAlphabet
      rcases h with h | h | h | h
      · rw [h]
        exact Finset.mem_image.mpr ⟨-4, by norm_num, by norm_num⟩
      · rw [h]
        exact Finset.mem_image.mpr ⟨-2, by norm_num, by norm_num⟩
      · rw [h]
        exact Finset.mem_image.mpr ⟨2, by norm_num, by norm_num⟩
      · rw [h]
        exact Finset.mem_image.mpr ⟨4, by norm_num, by norm_num⟩
  | inr a =>
    rcases a with ⟨e, t⟩
    change SubdivisionSchur.matrix (SourceRouting.data S precision) _ _
      (Sum.inr ⟨e, t⟩) (Sum.inr ⟨e, t⟩) ∈ diagonalAlphabet
    rw [SubdivisionSchur.matrix_internal_same]
    simpa only [Nat.add_one_ne_self, or_self, ↓reduceIte] using zero_mem_diagonalAlphabet

theorem diagonal_abs_le_three (S : Source.SparseSystem) (precision : ℕ)
    (a : SourceRouting.Vertex S precision) : |matrix S precision a a| ≤ 3 := by
  obtain ⟨k, hk, he⟩ := Finset.mem_image.mp (diagonal_alphabet S precision a)
  rw [← he, abs_le]
  have h := Finset.mem_Icc.mp hk
  have hlo : (-6 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h.1
  have hhi : (k : ℝ) ≤ 6 := by exact_mod_cast h.2
  constructor <;> linarith

end Maxwell.Composition.SourceSubdivision
