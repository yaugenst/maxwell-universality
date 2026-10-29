import Maxwell.Cost.SourceGrouping.Loop
import Maxwell.Logical.CachedNormalization

/-! The exact row blocks denoted by the finite pass's boundary markers.
Row-major order makes each semantic row filter one contiguous stream block. -/

namespace Maxwell.Cost.SourceGrouping

/-- A maximal row block is obtained by advancing to its row, then reading
until the row changes. Successive rows can share the advancing stream cursor. -/
def rowBlock {α : Type*} (row : α → ℕ) (i : ℕ) (entries : List α) : List α :=
  (entries.dropWhile fun p => decide (row p < i)).takeWhile fun p => row p == i

theorem rowBlock_eq_filter {α : Type*} (row : α → ℕ) (i : ℕ) (entries : List α)
    (hsorted : entries.Pairwise (fun p q => row p ≤ row q)) :
    rowBlock row i entries = entries.filter (fun p => row p == i) := by
  induction entries with
  | nil => rfl
  | cons p ps ih =>
      obtain ⟨hp, hps⟩ := List.pairwise_cons.mp hsorted
      have hi := ih hps
      by_cases hlt : row p < i
      · have hne : row p ≠ i := by omega
        simpa [rowBlock, hlt, hne] using hi
      · by_cases heq : row p = i
        · have hd : ps.dropWhile (fun q => decide (row q < i)) = ps := by
            cases ps with
            | nil => rfl
            | cons q qs =>
                have hq := hp q (by simp)
                have hnot : ¬ row q < i := by omega
                simp [hnot]
          have hi' : ps.takeWhile (fun q => row q == i) =
              ps.filter (fun q => row q == i) := by
            simpa only [rowBlock, hd] using hi
          simpa [rowBlock, heq] using congrArg (List.cons p) hi'
        · have hfilter : ps.filter (fun q => row q == i) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro q hq
            have hh := hp q hq
            simp only [beq_iff_eq]
            omega
          simp [rowBlock, hlt, heq, hfilter]

/-- Comparing canonical row words is exactly comparing the row numbers. -/
theorem bits_beq (a b : ℕ) : (a.bits == b.bits) = (a == b) := by
  by_cases h : a = b
  · subst b; simp
  · have hb : a.bits ≠ b.bits := by
      intro he
      have hh := congrArg addressValue he
      simp only [addressValue_bits] at hh
      exact h hh
    simp [h, hb]

def rowMarkers : ℕ → Bool → List LogEntries.Entry → List Bool
  | _, _, [] => []
  | previous, seen, p :: ps =>
      (!((p.1 == previous) && seen)) :: rowMarkers p.1 true ps

/-- This identity binds every marker emitted by the finite word-comparison
program to the corresponding actual row boundary. -/
theorem markers_numeric (previous : ℕ) (seen : Bool) (entries : List LogEntries.Entry) :
    markers previous.bits seen entries = rowMarkers previous seen entries := by
  induction entries generalizing previous seen with
  | nil => rfl
  | cons p ps ih => simp only [markers, rowMarkers, bits_beq, ih]

theorem markers_initial (entries : List LogEntries.Entry) :
    markers [] false entries = rowMarkers 0 false entries := by
  cases entries with
  | nil => rfl
  | cons p ps => simp only [markers, rowMarkers, Bool.and_false, Bool.not_false,
      markers_numeric]

/-- Within one equal-row run all subsequent marker bits are false. -/
theorem rowMarkers_constant (i : ℕ) (entries : List LogEntries.Entry)
    (h : ∀ p ∈ entries, p.1 = i) :
    rowMarkers i true entries = List.replicate entries.length false := by
  induction entries with
  | nil => rfl
  | cons p ps ih =>
      have hp := h p (by simp)
      have ht : ∀ q ∈ ps, q.1 = i := fun q hq => h q (List.mem_cons_of_mem p hq)
      simp [rowMarkers, hp, ih ht, List.replicate_succ]

theorem sourceEntries_rowBlock (S : Source.SparseSystem) (i : Fin S.n) :
    rowBlock (fun p : Fin S.n × Fin S.n => p.1.val) i.val (Codec.sourceEntries S) =
      Maxwell.Logical.Normalization.rowEntries S i := by
  rw [rowBlock_eq_filter _ _ _ (Codec.sourceEntries_rows_sorted S)]
  unfold Maxwell.Logical.Normalization.rowEntries
  apply List.filter_congr
  intro p _
  by_cases h : p.1 = i
  · simp [h]
  · have hn : p.1.val ≠ i.val := fun hh => h (Fin.ext hh)
    simp [h, hn]

theorem sourceRecord_rows_sorted (S : Source.SparseSystem) :
    (Codec.sourceRecord S).entries.Pairwise (fun p q => p.1 ≤ q.1) := by
  rw [Maxwell.Logical.CachedNormalization.sourceRecord_eq,
    Maxwell.Logical.CachedNormalization.stored_eq, List.map_map]
  rw [List.pairwise_map]
  exact Codec.sourceEntries_rows_sorted S

theorem sourceRecord_rowBlock (S : Source.SparseSystem) (i : ℕ) :
    rowBlock Prod.fst i (Codec.sourceRecord S).entries =
      (Codec.sourceRecord S).entries.filter (fun p => p.1 == i) :=
  rowBlock_eq_filter _ _ _ (sourceRecord_rows_sorted S)


theorem sourceRecord_rowBlock_values (S : Source.SparseSystem) (i : Fin S.n) :
    rowBlock Prod.fst i.val (Codec.sourceRecord S).entries =
      (Maxwell.Logical.Normalization.rowEntries S i).map
        (fun p => (p.1.val, p.2.val, S.matrix.toMatrix p.1 p.2)) := by
  rw [sourceRecord_rowBlock, Maxwell.Logical.CachedNormalization.sourceRecord_eq,
    Maxwell.Logical.CachedNormalization.stored_eq, List.map_map, List.filter_map]
  unfold Maxwell.Logical.Normalization.rowEntries
  congr 1

theorem sourceTerms_rows_sorted (S : Source.SparseSystem) (precision : ℕ) :
    (Maxwell.Logical.CachedNormalization.sourceTerms S precision).Pairwise
      (fun p q => p.1.val ≤ q.1.val) := by
  rw [Maxwell.Logical.CachedNormalization.sourceTerms_eq, List.pairwise_map]
  exact Codec.sourceEntries_rows_sorted S

/-- The cached dyadic stream has precisely the same contiguous row blocks
as the established compiler, and therefore needs no repeated row filtering. -/
theorem sourceTerms_rowBlock (S : Source.SparseSystem) (precision : ℕ) (i : Fin S.n) :
    (rowBlock (fun p => p.1.val) i.val
      (Maxwell.Logical.CachedNormalization.sourceTerms S precision)).map Prod.snd =
        Maxwell.Logical.Normalization.rowTerms S precision i := by
  rw [rowBlock_eq_filter _ _ _ (sourceTerms_rows_sorted S precision)]
  rw [← Maxwell.Logical.CachedNormalization.sourceTerms_row S precision i]
  congr 1

end Maxwell.Cost.SourceGrouping
