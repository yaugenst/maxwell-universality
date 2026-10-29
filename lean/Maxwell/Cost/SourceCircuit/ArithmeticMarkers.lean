import Maxwell.Cost.SourceCircuit.AllocateSource.Correspondence

namespace Maxwell.Cost.SourceCircuit.ArithmeticMarkers
open AllocateSource

/-- The wire carries one marker at each nonempty row's first coefficient. -/
def markerBlock {α : Type*} : List α → List Bool
  | [] => []
  | _::tail => true :: List.replicate tail.length false

def numericMarkers : ℕ → Bool → List ℕ → List Bool
  | _,_,[] => []
  | previous,seen,i::is => (!((i == previous) && seen)) :: numericMarkers i true is

theorem numeric_eq (previous : ℕ) (seen : Bool) (entries : List LogEntries.Entry) :
    SourceGrouping.rowMarkers previous seen entries = numericMarkers previous seen (entries.map Prod.fst) := by
  induction entries generalizing previous seen with
  | nil => rfl
  | cons e es ih => simp only [SourceGrouping.rowMarkers,numericMarkers,List.map_cons,ih]

theorem repeated_prefix (i : ℕ) (count : ℕ) (tail : List ℕ) :
    numericMarkers i true (List.replicate count i ++ tail) =
      List.replicate count false ++ numericMarkers i true tail := by
  induction count with
  | zero => simp
  | succ count ih => simp [List.replicate_succ,numericMarkers,ih]

theorem block_prefix {α : Type*} (key : α → ℕ) (i previous : ℕ) (seen : Bool)
    (block : List α) (tail : List ℕ) (hne : block ≠ [])
    (hall : ∀ x ∈ block, key x = i) (hprev : seen = false ∨ previous ≠ i) :
    numericMarkers previous seen (block.map key ++ tail) =
      markerBlock block ++ numericMarkers i true tail := by
  cases block with
  | nil => contradiction
  | cons x xs =>
    have hx := hall x (by simp)
    have hm : xs.map key = List.replicate xs.length i := by
      rw [← show (xs.map key).length = xs.length by simp]
      apply List.eq_replicate_length.mpr
      intro j hj
      obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hj
      exact hall y (by simp [hy])
    have hb : (!((i == previous) && seen)) = true := by
      rcases hprev with hs | hi
      · simp [hs]
      · have hn : i ≠ previous := Ne.symm hi
        simp [hn]
    simp only [List.map_cons,List.cons_append,numericMarkers,hx,hb,hm,markerBlock,
      List.cons_append,repeated_prefix]

theorem distinct_blocks {α : Type*} (key : α → ℕ) (ids : List ℕ) (block : ℕ → List α)
    (previous : ℕ) (seen : Bool) (hids : ids.Nodup)
    (hprev : seen = false ∨ previous ∉ ids)
    (hne : ∀ i ∈ ids, block i ≠ [])
    (hall : ∀ i ∈ ids, ∀ x ∈ block i, key x = i) :
    numericMarkers previous seen ((ids.flatMap block).map key) =
      ids.flatMap (fun i => markerBlock (block i)) := by
  induction ids generalizing previous seen with
  | nil => rfl
  | cons i ids ih =>
    obtain ⟨hi,hids⟩ := List.nodup_cons.mp hids
    have hpi : seen = false ∨ previous ≠ i := by
      rcases hprev with hs | hn
      · exact Or.inl hs
      · exact Or.inr (fun he => hn (by simp [he]))
    rw [List.flatMap_cons,List.map_append,block_prefix key i previous seen (block i)
      ((ids.flatMap block).map key) (hne i (by simp)) (hall i (by simp)) hpi]
    rw [ih i true hids (Or.inr hi) (fun j hj => hne j (by simp [hj]))
      (fun j hj => hall j (by simp [hj]))]
    rfl

def row (S : Source.SparseSystem) (p i : ℕ) : List (AllocationPass.Record S.n) :=
  (records S p).filter (fun r => decide (r.row = i))

def rows (S : Source.SparseSystem) (p : ℕ) : List (List (AllocationPass.Record S.n)) :=
  (List.range S.n).map (row S p)

def recordTerm {n : ℕ} (r : AllocationPass.Record n) : Logical.DyadicTerm n :=
  ⟨r.bits,r.negative,r.column⟩

theorem records_sorted (S : Source.SparseSystem) (p : ℕ) :
    (records S p).Pairwise (fun r q => r.row ≤ q.row) := by
  rw [records,List.pairwise_map]
  exact SourceGrouping.sourceTerms_rows_sorted S p

theorem rows_flatten (S : Source.SparseSystem) (p : ℕ) : (rows S p).flatten = records S p := by
  have h := sorted_rows_flatMap (fun r : AllocationPass.Record S.n => r.row) (records S p) 0 S.n
    (records_sorted S p) (fun r hr => ⟨Nat.zero_le _,by simpa using records_row S p r hr⟩)
  change (List.range S.n).flatMap (row S p) = records S p
  rw [List.range_eq_range']
  exact h

theorem row_nonempty (S : Source.SparseSystem) (p : ℕ) (hunit : IsUnit (Source.realMatrix S))
    (i : Fin S.n) : row S p i.val ≠ [] := by
  obtain ⟨j,hj⟩ := Source.row_has_nonzero S hunit i
  have hm := (Codec.mem_sourceEntries S (i,j)).mpr
    ((SparseRationalMatrix.toMatrix_ne_zero_iff S.matrix i j).mp hj)
  have hr : (⟨i.val,j,(Logical.Normalization.dyadicTerm p
      (Logical.Normalization.normalizedMatrix S i j) j).negative,
      (Logical.Normalization.dyadicTerm p (Logical.Normalization.normalizedMatrix S i j) j).bits⟩ :
      AllocationPass.Record S.n) ∈ row S p i.val := by
    simp only [row,records,Logical.CachedNormalization.sourceTerms_eq,List.map_map,List.mem_filter]
    refine ⟨List.mem_map.mpr ⟨(i,j),hm,?_⟩,by simp⟩
    rfl
  intro he
  rw [he] at hr
  simp at hr

theorem source_keys (S : Source.SparseSystem) (p : ℕ) :
    (records S p).map AllocationPass.Record.row = (Codec.sourceRecord S).entries.map Prod.fst := by
  simp only [records,Logical.CachedNormalization.sourceTerms_eq,
    Logical.CachedNormalization.sourceRecord_eq,Logical.CachedNormalization.stored_eq,List.map_map]
  rfl

theorem source_markers (S : Source.SparseSystem) (p : ℕ) (hunit : IsUnit (Source.realMatrix S)) :
    SourceGrouping.markers [] false (Codec.sourceRecord S).entries =
      (rows S p).flatMap markerBlock := by
  rw [SourceGrouping.markers_initial,numeric_eq,← source_keys S p,← rows_flatten S p]
  unfold rows
  rw [← List.flatMap_def]
  simpa only [List.flatMap_map] using distinct_blocks AllocationPass.Record.row
    (List.range S.n) (row S p) 0 false List.nodup_range (Or.inl rfl)
    (fun i hi => row_nonempty S p hunit ⟨i,List.mem_range.mp hi⟩)
    (fun _ _ _ hx => by simpa [row] using (List.mem_filter.mp hx).2)

theorem rows_nonempty (S : Source.SparseSystem) (p : ℕ) (hunit : IsUnit (Source.realMatrix S)) :
    ∀ rs ∈ rows S p, rs ≠ [] := by
  intro rs hrs
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hrs
  exact row_nonempty S p hunit ⟨i,List.mem_range.mp hi⟩


theorem row_terms (S : Source.SparseSystem) (p : ℕ) (i : Fin S.n) :
    (row S p i.val).map recordTerm = Logical.Normalization.rowTerms S p i := by
  rw [← Logical.CachedNormalization.sourceTerms_row]
  simp only [row,records,List.filter_map,List.map_map]
  change ((Logical.CachedNormalization.sourceTerms S p).filter
    (fun t => decide (t.1.val = i.val))).map Prod.snd = _
  congr 1

theorem rows_terms (S : Source.SparseSystem) (p : ℕ) :
    (rows S p).map (List.map recordTerm) = Logical.Normalization.sourceRows S p := by
  have hind : (List.finRange S.n).map Fin.val = List.range S.n := by
    ext i
    simp
  rw [rows,← hind,List.map_map,List.map_map,Logical.Normalization.sourceRows,List.ofFn_eq_map]
  apply List.map_congr_left
  intro i _
  exact row_terms S p i

theorem markerBlock_count {α : Type*} (xs : List α) (h : xs ≠ []) :
    (markerBlock xs).count true = 1 := by
  cases xs with
  | nil => contradiction
  | cons x xs => simp [markerBlock,List.count_replicate]

theorem blocks_count {α : Type*} (rs : List (List α)) (h : ∀ r ∈ rs, r ≠ []) :
    (rs.flatMap markerBlock).count true = rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.flatMap_cons,List.count_append,markerBlock_count r (h r (by simp)),
      ih (fun q hq => h q (by simp [hq])),List.length_cons]
    omega

theorem source_markers_count (S : Source.SparseSystem) (p : ℕ)
    (hunit : IsUnit (Source.realMatrix S)) :
    (SourceGrouping.markers [] false (Codec.sourceRecord S).entries).count true = S.n := by
  rw [source_markers S p hunit,blocks_count _ (rows_nonempty S p hunit)]
  simp [rows]

end Maxwell.Cost.SourceCircuit.ArithmeticMarkers
