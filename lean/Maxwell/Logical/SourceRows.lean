import Maxwell.Logical.Normalization
import Maxwell.Logical.Forest

/-! Sparse source entries become the actual signed dyadic row expressions. -/

namespace Maxwell.Logical.Normalization

def rowEntries (S : Source.SparseSystem) (i : Fin S.n) : List (Fin S.n × Fin S.n) :=
  (Codec.sourceEntries S).filter fun p => p.1 == i

def rowTerms (S : Source.SparseSystem) (precision : ℕ) (i : Fin S.n) :
    List (DyadicTerm S.n) :=
  (rowEntries S i).map fun p => dyadicTerm precision (normalizedMatrix S p.1 p.2) p.2

def sourceRows (S : Source.SparseSystem) (precision : ℕ) : List (List (DyadicTerm S.n)) :=
  List.ofFn (rowTerms S precision)

@[simp] theorem sourceRows_length (S : Source.SparseSystem) (precision : ℕ) :
    (sourceRows S precision).length = S.n := by simp [sourceRows]

theorem rowTerms_precision (S : Source.SparseSystem) (precision : ℕ) (i : Fin S.n)
    (term : DyadicTerm S.n) (h : term ∈ rowTerms S precision i) :
    term.bits.length = precision := by
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp h
  exact dyadicTerm_length _ _ _

theorem sourceRows_precision (S : Source.SparseSystem) (precision : ℕ)
    (row : List (DyadicTerm S.n)) (hr : row ∈ sourceRows S precision)
    (term : DyadicTerm S.n) (ht : term ∈ row) : term.bits.length = precision := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
  exact rowTerms_precision S precision i term ht

theorem sum_filter_row_length {n : ℕ} (entries : List (Fin n × Fin n)) :
    ∑ i : Fin n, (entries.filter fun p => p.1 == i).length = entries.length := by
  induction entries with
  | nil => simp
  | cons p ps ih =>
      have heq (i : Fin n) : ((p :: ps).filter fun q => q.1 == i).length =
          (if i = p.1 then 1 else 0) + (ps.filter fun q => q.1 == i).length := by
        by_cases h : i = p.1
        · subst i
          simp [Nat.add_comm]
        · have h' : p.1 ≠ i := Ne.symm h
          simp [h, h']
      simp_rw [heq]
      rw [Finset.sum_add_distrib, ih]
      simp [Nat.add_comm]

theorem sourceRows_term_count (S : Source.SparseSystem) (precision : ℕ) :
    ((sourceRows S precision).map List.length).sum = S.nnz := by
  simp only [sourceRows, List.map_ofFn, List.sum_ofFn, Function.comp_apply,
    rowTerms, List.length_map,
    rowEntries]
  rw [sum_filter_row_length, Codec.sourceEntries_length]

theorem rowEntries_nodup (S : Source.SparseSystem) (i : Fin S.n) :
    (rowEntries S i).Nodup := by
  apply List.Nodup.filter
  unfold Codec.sourceEntries
  exact Finset.sort_nodup _ _

theorem mem_rowEntries (S : Source.SparseSystem) (i : Fin S.n) (p : Fin S.n × Fin S.n) :
    p ∈ rowEntries S i ↔ p ∈ S.matrix.support ∧ p.1 = i := by
  simp [rowEntries, Codec.mem_sourceEntries]

theorem rowTerms_semantics (S : Source.SparseSystem) (hm : 2 ≤ S.nnz)
    (precision : ℕ) (hs : 1 ≤ precision) (i : Fin S.n) (values : Fin S.n → ℝ) :
    (rowExpression (rowTerms S precision i)).evaluate values =
      ((rowEntries S i).map fun p =>
        ((Rounding.nearest precision (normalizedMatrix S p.1 p.2)).value : ℝ) *
          values p.2).sum := by
  rw [rowExpression_correct, rowTerms, List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  change ((dyadicTerm precision (normalizedMatrix S p.1 p.2) p.2).coefficient : ℝ) *
    values p.2 = _
  rw [dyadicTerm_coefficient precision hs _ (normalizedMatrix_half_bound S hm p.1 p.2)]

theorem rowTerms_matrix_semantics (S : Source.SparseSystem) (hm : 2 ≤ S.nnz)
    (precision : ℕ) (hs : 1 ≤ precision) (i : Fin S.n) (values : Fin S.n → ℝ) :
    (rowExpression (rowTerms S precision i)).evaluate values =
      ∑ j, ((Rounding.matrix precision (normalizedMatrix S) i j : ℚ) : ℝ) * values j := by
  rw [rowTerms_semantics S hm precision hs]
  rw [← List.sum_toFinset _ (rowEntries_nodup S i)]
  have heq : (rowEntries S i).toFinset = S.matrix.support.filter (fun p => p.1 = i) := by
    ext p
    simp [mem_rowEntries]
  rw [heq, Finset.sum_filter]
  let f : Fin S.n × Fin S.n → ℝ := fun p =>
    if p.1 = i then ((Rounding.nearest precision (normalizedMatrix S p.1 p.2)).value : ℝ) *
      values p.2 else 0
  change ∑ p ∈ S.matrix.support, f p = _
  have hsum : ∑ p ∈ S.matrix.support, f p = ∑ p : Fin S.n × Fin S.n, f p := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro p _ hp
    have hz : S.matrix.toMatrix p.1 p.2 = 0 := by
      by_contra hn
      exact hp ((SparseRationalMatrix.toMatrix_ne_zero_iff S.matrix p.1 p.2).mp hn)
    simp [f, normalizedMatrix_zero S p.1 p.2 hz]
  rw [hsum, Fintype.sum_prod_type]
  simp [f, Rounding.matrix]

end Maxwell.Logical.Normalization
