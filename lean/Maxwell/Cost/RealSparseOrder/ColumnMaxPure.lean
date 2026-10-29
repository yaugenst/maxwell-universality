import Maxwell.Cost.RealSparseOrder.Buffer

namespace Maxwell.Cost.RealSparseOrder.ColumnMax

def columnCount : List SparseEntry→ℕ
  | [] => 0
  | e::es => max (e.column+1) (columnCount es)

theorem column_lt (es : List SparseEntry) (e : SparseEntry) (he : e∈es) :
    e.column<columnCount es := by
  induction es with
  | nil => simp at he
  | cons f es ih =>
    rcases List.mem_cons.mp he with rfl|he
    · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
    · exact (ih he).trans_le (le_max_right _ _)

theorem columnCount_le (es : List SparseEntry) (n : ℕ) (h : ∀e∈es,e.column<n) :
    columnCount es≤n := by
  induction es with
  | nil => exact Nat.zero_le _
  | cons e es ih =>
    exact max_le (by have hh:=h e (by simp); omega) (ih (fun f hf=>h f (by simp [hf])))

/-- Every represented column has the stated upper bound, and a represented
last column forces the maximum to attain that bound. -/
theorem columnCount_eq (es : List SparseEntry) (n : ℕ)
    (h : ∀e∈es,e.column<n) (hlast : n=0 ∨∃e∈es,e.column+1=n) : columnCount es=n := by
  have hu := columnCount_le es n h
  rcases hlast with rfl|⟨e,he,hn⟩
  · omega
  · have hl := column_lt es e he
    omega

end Maxwell.Cost.RealSparseOrder.ColumnMax
