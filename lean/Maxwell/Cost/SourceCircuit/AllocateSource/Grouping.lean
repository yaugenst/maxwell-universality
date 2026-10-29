import Maxwell.Cost.SourceCircuit.AllocateSource.Data
import Maxwell.Cost.SourceGrouping.Semantics
import Maxwell.Logical.ForestLinearize

namespace Maxwell.Cost.SourceCircuit.AllocateSource

private theorem sorted_split {α : Type*} (row : α → ℕ) (xs : List α) (k : ℕ)
    (hs : xs.Pairwise (fun a b => row a ≤ row b))
    (hl : ∀ x ∈ xs, k ≤ row x) :
    xs.filter (fun x => decide (row x = k)) ++
      xs.filter (fun x => decide (k < row x)) = xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hx,hxs⟩ := List.pairwise_cons.mp hs
    have hlo := hl x (by simp)
    by_cases he : row x = k
    · have ht := ih hxs (fun y hy => hl y (by simp [hy]))
      simpa [he] using congrArg (List.cons x) ht
    · have hgt : k < row x := by omega
      have hall (y : α) (hy : y ∈ xs) : k < row y := by have := hx y hy; omega
      have hf : xs.filter (fun y => decide (row y = k)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro y hy
        have := hall y hy
        simp only [Bool.not_eq_true,decide_eq_false_iff_not]
        omega
      have hg : xs.filter (fun y => decide (k < row y)) = xs := by
        apply List.filter_eq_self.mpr
        intro y hy
        exact decide_eq_true (hall y hy)
      simp [he,hgt,hf,hg]

/-- Concatenating ordered row filters reconstructs the original stream,
including its order within a row. -/
theorem sorted_rows_flatMap {α : Type*} (row : α → ℕ) (xs : List α) (k n : ℕ)
    (hs : xs.Pairwise (fun a b => row a ≤ row b))
    (hr : ∀ x ∈ xs, k ≤ row x ∧ row x < k+n) :
    (List.range' k n).flatMap (fun i => xs.filter (fun x => decide (row x = i))) = xs := by
  induction n generalizing k xs with
  | zero =>
    have hempty : xs = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro x hx
      have := hr x hx
      omega
    simp [hempty]
  | succ n ih =>
    let tail := xs.filter (fun x => decide (k < row x))
    have htail : tail.Pairwise (fun a b => row a ≤ row b) := hs.filter _
    have htailRange : ∀ x ∈ tail, k+1 ≤ row x ∧ row x < k+1+n := by
      intro x hx
      obtain ⟨hmem,hgt⟩ := List.mem_filter.mp hx
      have hh := hr x hmem
      have ht : k < row x := by simpa using hgt
      omega
    have hi := ih tail (k+1) htail htailRange
    have he : (List.range' (k+1) n).flatMap (fun i => xs.filter (fun x => decide (row x = i))) =
        (List.range' (k+1) n).flatMap (fun i => tail.filter (fun x => decide (row x = i))) := by
      apply congrArg List.flatten
      apply List.map_congr_left
      intro i hi
      have hk : k < i := by obtain ⟨j,_,hj⟩ := List.mem_range'.mp hi; omega
      dsimp [tail]
      rw [List.filter_filter]
      apply List.filter_congr
      intro x _
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true,decide_eq_true_eq]
      omega
    rw [List.range'_succ,List.flatMap_cons,he,hi]
    exact sorted_split row xs k hs (fun x hx => (hr x hx).1)

theorem sourceRows_flatten (S : Source.SparseSystem) (p : ℕ) :
    (Logical.Normalization.sourceRows S p).flatten =
      (Logical.CachedNormalization.sourceTerms S p).map Prod.snd := by
  let xs := Logical.CachedNormalization.sourceTerms S p
  have h := sorted_rows_flatMap (fun t : Fin S.n × Logical.DyadicTerm S.n => t.1.val)
    xs 0 S.n (SourceGrouping.sourceTerms_rows_sorted S p)
    (fun x _ => ⟨Nat.zero_le _,by simp⟩)
  have hf : (List.finRange S.n).flatMap (fun i =>
      (xs.filter (fun t => t.1 == i)).map Prod.snd) = xs.map Prod.snd := by
    rw [← List.map_flatMap]
    apply congrArg (List.map Prod.snd)
    have hind : (List.finRange S.n).map Fin.val = List.range' 0 S.n := by
      ext i
      simp [List.range_eq_range']
    rw [← hind,List.flatMap_map] at h
    exact h
  have hrows : Logical.Normalization.sourceRows S p = (List.finRange S.n).map
      (fun i => (xs.filter (fun t => t.1 == i)).map Prod.snd) := by
    rw [Logical.Normalization.sourceRows,List.ofFn_eq_map]
    apply List.map_congr_left
    intro i _
    exact (Logical.CachedNormalization.sourceTerms_row S p i).symm
  rw [hrows,← List.flatMap_def]
  exact hf

end Maxwell.Cost.SourceCircuit.AllocateSource
