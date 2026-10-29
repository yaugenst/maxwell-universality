import Maxwell.Cost.RealSparseOrder.Order

namespace Maxwell.Cost.RealSparseOrder.Relabel

def nextCount (previous : Option ℕ) (count row : ℕ) : ℕ :=
  if previous=some row then count else count+1

/-- Original labels retained when entering each new consecutive row group. -/
def retained (previous : Option ℕ) : List SparseEntry → List ℕ
  | [] => []
  | e::es => if previous=some e.row then retained (some e.row) es
    else e.row::retained (some e.row) es

def relabeled (previous : Option ℕ) (count : ℕ) : List SparseEntry → List SparseEntry
  | [] => []
  | e::es =>
    let c := nextCount previous count e.row
    {e with row := c-1}::relabeled (some e.row) c es

def lastRow (previous : Option ℕ) : List SparseEntry → Option ℕ
  | [] => previous
  | e::es => lastRow (some e.row) es

@[simp] theorem relabeled_length (previous : Option ℕ) (count : ℕ) (es : List SparseEntry) :
    (relabeled previous count es).length=es.length := by
  induction es generalizing previous count with
  | nil => rfl
  | cons e es ih => simp [relabeled,ih]

theorem retained_length_le (previous : Option ℕ) (es : List SparseEntry) :
    (retained previous es).length≤es.length := by
  induction es generalizing previous with
  | nil => simp [retained]
  | cons e es ih =>
    have h := ih (some e.row)
    simp only [retained,List.length_cons]
    split
    · omega
    · simp only [List.length_cons]; omega

theorem retained_count (previous : Option ℕ) (count : ℕ) (e : SparseEntry) (es : List SparseEntry) :
    nextCount previous count e.row+(retained (some e.row) es).length=
      count+(retained previous (e::es)).length := by
  simp only [nextCount,retained]
  split
  · rfl
  · simp only [List.length_cons]; omega

theorem relabeled_columns_values (previous : Option ℕ) (count : ℕ) (es : List SparseEntry) :
    (relabeled previous count es).map (fun e=>(e.column,e.value))=
      es.map (fun e=>(e.column,e.value)) := by
  induction es generalizing previous count with
  | nil => rfl
  | cons e es ih => simp [relabeled,ih]

theorem nextCount_pos {previous : Option ℕ} {count row : ℕ}
    (h : previous≠none→0<count) : 0<nextCount previous count row := by
  unfold nextCount
  split
  · rename_i he
    exact h (by rw [he]; simp)
  · omega

theorem relabeled_row_lt (previous : Option ℕ) (count : ℕ) (es : List SparseEntry)
    (hcount : previous≠none→0<count) :
    ∀e∈relabeled previous count es, e.row<count+(retained previous es).length := by
  induction es generalizing previous count with
  | nil => simp [relabeled]
  | cons e es ih =>
    have hc := nextCount_pos (row:=e.row) hcount
    have ht := ih (some e.row) (nextCount previous count e.row) (fun _=>hc)
    intro f hf
    simp only [relabeled,List.mem_cons] at hf
    rcases hf with rfl|hf
    · have hh := retained_count previous count e es
      change nextCount previous count e.row-1<_
      omega
    · rw [←retained_count previous count e es]
      exact ht f hf

theorem retained_mem {previous : Option ℕ} {es : List SparseEntry} {row : ℕ}
    (h : row∈retained previous es) : ∃e∈es,e.row=row := by
  induction es generalizing previous with
  | nil => simp [retained] at h
  | cons e es ih =>
    simp only [retained] at h
    split at h
    · obtain ⟨f,hf,he⟩ := ih h
      exact ⟨f,List.mem_cons_of_mem _ hf,he⟩
    · rcases List.mem_cons.mp h with he|ht
      · exact ⟨e,by simp,he.symm⟩
      · obtain ⟨f,hf,he⟩ := ih ht
        exact ⟨f,List.mem_cons_of_mem _ hf,he⟩

/-- A row either is the already active row or appears in the newly
emitted map. At the initial state every original row is therefore retained. -/
theorem original_row_retained (previous : Option ℕ) (es : List SparseEntry) :
    ∀e∈es,previous=some e.row ∨e.row∈retained previous es := by
  induction es generalizing previous with
  | nil => simp
  | cons e es ih =>
    intro f hf
    rcases List.mem_cons.mp hf with heq|hf
    · subst f
      by_cases he : previous=some e.row
      · exact Or.inl he
      · exact Or.inr (by simp [retained,he])
    · rcases ih (some e.row) f hf with he|ht
      · have hrow : e.row=f.row := Option.some.inj he
        by_cases hp : previous=some e.row
        · exact Or.inl (by simpa only [hrow] using hp)
        · exact Or.inr (by rw [retained,ite_eq_right hp]; exact List.mem_cons.mpr (Or.inl hrow.symm))
      · exact Or.inr (by by_cases hp : previous=some e.row <;> simp [retained,hp,ht])

theorem initial_row_retained (es : List SparseEntry) (e : SparseEntry) (he : e∈es) :
    e.row∈retained none es := by
  simpa using original_row_retained none es e he

end Maxwell.Cost.RealSparseOrder.Relabel
