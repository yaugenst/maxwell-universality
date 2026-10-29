import Maxwell.Cost.RealSparseOrder.Preprocess
import Maxwell.Cost.RealSparseOrder.RelabelOrder
import Maxwell.Cost.RealSparseOrder.ColumnMaxMeaning

namespace Maxwell.Cost.RealSparseOrder.Preprocess

@[simp] theorem entries_length (es : List SparseEntry) : (ActiveRows.entries es).length=es.length := by
  simp only [ActiveRows.entries,Relabel.relabeled_length,bottomUpSort_length]

theorem entries_sorted (es : List SparseEntry) : (ActiveRows.entries es).Pairwise KeyLE :=
  Relabel.initial_sorted (bottomUpSort es) (bottomUpSort_sorted es)

theorem entries_key_nodup (es : List SparseEntry) (h : (es.map fun e=>(e.row,e.column)).Nodup) :
    ((ActiveRows.entries es).map fun e=>(e.row,e.column)).Nodup := by
  apply Relabel.initial_key_nodup
  exact ((bottomUpSort_perm es).map _).nodup_iff.mpr h

theorem retained_strict (es : List SparseEntry) : (ActiveRows.retained es).Pairwise (· < ·) :=
  Relabel.retained_strict none (bottomUpSort es) (bottomUpSort_sorted es)

theorem recovery (es : List SparseEntry) :
    List.Forall₂ (fun old new=>(ActiveRows.retained es)[new.row]?=some old.row ∧
      new.column=old.column ∧new.value=old.value) (bottomUpSort es) (ActiveRows.entries es) :=
  Relabel.initial_recovery (bottomUpSort es)

theorem entries_nonzero (es : List SparseEntry) (h : ∀e∈es,e.value≠0) :
    ∀e∈ActiveRows.entries es,e.value≠0 := by
  intro e he
  obtain ⟨i,hi,hei⟩ := List.getElem_of_mem he
  have ho : i<(bottomUpSort es).length := by simpa only [ActiveRows.entries,Relabel.relabeled_length] using hi
  have hr := (recovery es).get ho hi
  have hold : (bottomUpSort es)[i]∈es :=
    (bottomUpSort_perm es).mem_iff.mp (List.getElem_mem ho)
  have hv : (ActiveRows.entries es)[i].value=(bottomUpSort es)[i].value := hr.2.2
  rw [←hei,hv]
  exact h _ hold

theorem column_count (es : List SparseEntry) :
    ColumnMax.columnCount (ActiveRows.entries es)=ColumnMax.columnCount es := by
  rw [ActiveRows.entries,Relabel.columnCount_relabeled,ColumnMax.columnCount_bottomUpSort]

theorem Result.original_columns {es : List SparseEntry} {vector : ℕ→ℝ} {s t : RAMState}
    (h : Result es vector s t) : t.indices 42=ColumnMax.columnCount es :=
  h.columns.trans (column_count es)

/-- Full-column input support supplies the dimension through the actual
maximum scan, rather than uncharged metadata. -/
theorem Result.dimension {es : List SparseEntry} {vector : ℕ→ℝ} {s t : RAMState}
    (h : Result es vector s t) (n : ℕ) (hcols : ∀e∈es,e.column<n)
    (hlast : n=0 ∨∃e∈es,e.column+1=n) : t.indices 42=n :=
  h.original_columns.trans (ColumnMax.columnCount_eq es n hcols hlast)

theorem Result.rows_bound {es : List SparseEntry} {vector : ℕ→ℝ} {s t : RAMState}
    (h : Result es vector s t) : t.indices 35≤es.length := h.active.rank_le

theorem Result.all_rows_active {es : List SparseEntry} {vector : ℕ→ℝ} {s t : RAMState}
    (h : Result es vector s t) (i : ℕ) (hi : i<t.indices 35) :
    ∃e∈ActiveRows.entries es,e.row=i := by
  rw [h.active.rankCount] at hi
  exact Relabel.initial_rank_surjective (bottomUpSort es) i hi

end Maxwell.Cost.RealSparseOrder.Preprocess
