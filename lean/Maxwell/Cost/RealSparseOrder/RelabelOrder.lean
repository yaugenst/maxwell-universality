import Maxwell.Cost.RealSparseOrder.RelabelMeaning
import Maxwell.Cost.RealSparseOrder.ColumnMaxPure
import Mathlib.Data.List.Forall2

namespace Maxwell.Cost.RealSparseOrder.Relabel

private theorem keyLE_of_recovery {labels : List ℕ}
    (hl : labels.Pairwise (· < ·)) {a b a' b' : SparseEntry}
    (ha : labels[a'.row]? = some a.row) (hb : labels[b'.row]? = some b.row)
    (hca : a'.column = a.column) (hcb : b'.column = b.column)
    (h : KeyLE a b) : KeyLE a' b' := by
  obtain ⟨hai, hav⟩ := List.getElem?_eq_some_iff.mp ha
  obtain ⟨hbi, hbv⟩ := List.getElem?_eq_some_iff.mp hb
  by_cases hlt : a'.row < b'.row
  · exact Or.inl hlt
  have he : a'.row = b'.row := by
    by_contra hne
    have hrev : b'.row < a'.row := by omega
    have hh := hl.rel_getElem_of_lt hbi hai hrev
    rw [hav, hbv] at hh
    unfold KeyLE at h
    omega
  have hab : a.row = b.row := Option.some.inj
    (ha.symm.trans ((congrArg (fun r => labels[r]?) he).trans hb))
  refine Or.inr ⟨he, ?_⟩
  rw [hca, hcb]
  unfold KeyLE at h
  omega

/-- Ranking the active row labels preserves row-major order. -/
theorem initial_sorted (es : List SparseEntry) (hs : es.Pairwise KeyLE) :
    (relabeled none 0 es).Pairwise KeyLE := by
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij
  have hio : i < es.length := by simpa using hi
  have hjo : j < es.length := by simpa using hj
  have hri := (initial_recovery es).get hio hi
  have hrj := (initial_recovery es).get hjo hj
  exact keyLE_of_recovery (retained_strict none es hs) hri.1 hrj.1
    hri.2.1 hrj.2.1 (hs.rel_getElem_of_lt hio hjo hij)

/-- Distinct row-column keys remain distinct after active-row ranking. -/
theorem initial_key_nodup (es : List SparseEntry)
    (hn : (es.map fun e => (e.row, e.column)).Nodup) :
    ((relabeled none 0 es).map fun e => (e.row, e.column)).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at hn ⊢
  apply List.pairwise_iff_getElem.mpr
  intro i j hi hj hij he
  have hio : i < es.length := by simpa using hi
  have hjo : j < es.length := by simpa using hj
  have hri := (initial_recovery es).get hio hi
  have hrj := (initial_recovery es).get hjo hj
  have hrow := congrArg Prod.fst he
  have hcol := congrArg Prod.snd he
  have holdrow : es[i].row = es[j].row := Option.some.inj
    (hri.1.symm.trans
      ((congrArg (fun r => (retained none es)[r]?) hrow).trans hrj.1))
  have holdcol : es[i].column = es[j].column :=
    hri.2.1.symm.trans (hcol.trans hrj.2.1)
  exact hn.rel_getElem_of_lt hio hjo hij (Prod.ext holdrow holdcol)

/-- Relabeling changes only row labels, so the required column count is exact. -/
theorem columnCount_relabeled (previous : Option ℕ) (count : ℕ)
    (es : List SparseEntry) :
    ColumnMax.columnCount (relabeled previous count es) = ColumnMax.columnCount es := by
  induction es generalizing previous count with
  | nil => rfl
  | cons e es ih =>
    simp only [relabeled, ColumnMax.columnCount, ih]

end Maxwell.Cost.RealSparseOrder.Relabel
