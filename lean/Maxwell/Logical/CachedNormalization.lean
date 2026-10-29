import Maxwell.Logical.SourceRows
import Maxwell.Codec.Source

/-! Sparse coefficient normalization with one saved input stream and one
saved matrix scale. Stored coefficients are read directly through erased
support proofs, rather than looking them up in the dense matrix view. -/

namespace Maxwell.Logical.CachedNormalization
open Normalization

abbrev Stored (n : ℕ) := Fin n × Fin n × ℚ

def stored (S : Source.SparseSystem) : List (Stored S.n) :=
  (Codec.sourceEntries S).attach.map fun p =>
    (p.val.1, p.val.2, S.matrix.coefficient ⟨p.val, (Codec.mem_sourceEntries S p.val).mp p.property⟩)

theorem stored_eq (S : Source.SparseSystem) : stored S =
    (Codec.sourceEntries S).map (fun p => (p.1, p.2, S.matrix.toMatrix p.1 p.2)) := by
  rw [stored]
  conv_rhs => rw [← List.attach_map_val]
  apply List.map_congr_left
  intro p _
  congr 2
  exact (SparseRationalMatrix.toMatrix_at_stored S.matrix p.val.1 p.val.2
    ((Codec.mem_sourceEntries S p.val).mp p.property)).symm

@[simp] theorem stored_length (S : Source.SparseSystem) : (stored S).length = S.nnz := by
  simp [stored, Codec.sourceEntries_length]

def matrixScaleOf {n : ℕ} (entries : List (Stored n)) : ℚ :=
  entries.length * magnitudeMax (entries.map fun p => p.2.2)

theorem matrixScaleOf_stored (S : Source.SparseSystem) : matrixScaleOf (stored S) = matrixScale S := by
  simp [matrixScaleOf, stored_eq, matrixScale, matrixMax, matrixValues, Codec.sourceEntries_length, Function.comp_def]

/-- The outer let shares the maximum and scale across all m coefficients. -/
def normalize {n : ℕ} (precision : ℕ) (entries : List (Stored n)) : List (Fin n × DyadicTerm n) :=
  let scale := matrixScaleOf entries
  entries.map fun p => (p.1, dyadicTerm precision (p.2.2 / scale) p.2.1)

def sourceTerms (S : Source.SparseSystem) (precision : ℕ) : List (Fin S.n × DyadicTerm S.n) :=
  normalize precision (stored S)

@[simp] theorem sourceTerms_length (S : Source.SparseSystem) (precision : ℕ) :
    (sourceTerms S precision).length = S.nnz := by
  simp [sourceTerms, normalize]

theorem sourceTerms_eq (S : Source.SparseSystem) (precision : ℕ) :
    sourceTerms S precision = (Codec.sourceEntries S).map (fun p =>
      (p.1, dyadicTerm precision (normalizedMatrix S p.1 p.2) p.2)) := by
  unfold sourceTerms normalize
  rw [matrixScaleOf_stored, stored_eq, List.map_map]
  rfl

/-- Selecting one stored row gives exactly the established semantic compiler row. -/
theorem sourceTerms_row (S : Source.SparseSystem) (precision : ℕ) (i : Fin S.n) :
    ((sourceTerms S precision).filter fun p => p.1 == i).map Prod.snd = rowTerms S precision i := by
  rw [sourceTerms_eq]
  simp only [List.filter_map, List.map_map, rowTerms, rowEntries, Function.comp_def]

/-- The stream retained by the finite parser is this same direct coefficient stream. -/
theorem sourceRecord_eq (S : Source.SparseSystem) : (Codec.sourceRecord S).entries =
    (stored S).map (fun p => (p.1.val, p.2.1.val, p.2.2)) := by
  simp only [Codec.sourceRecord, stored, List.map_map]
  rfl

end Maxwell.Logical.CachedNormalization
