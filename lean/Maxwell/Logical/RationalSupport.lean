import Maxwell.Logical.RationalValidity

namespace Maxwell.Logical.RationalCode

theorem entrySum_zero_of_not_mem (es : List Entry) (i j : ℕ)
    (h : (i, j) ∉ es.map Entry.key) : entrySum es i j = 0 := by
  apply List.sum_eq_zero
  intro a ha
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
  have hn : ¬(e.row = i ∧ e.column = j) := by
    intro hp
    exact h (List.mem_map.mpr ⟨e, he, Prod.ext hp.1 hp.2⟩)
  simp [hn]

theorem entrySum_at_entry (es : List Entry) (hn : (es.map Entry.key).Nodup)
    (e : Entry) (he : e ∈ es) : entrySum es e.row e.column = e.value := by
  induction es with
  | nil => simp at he
  | cons a es ih =>
      have hnodup := List.nodup_cons.mp hn
      rcases List.mem_cons.mp he with he | he
      · subst e
        rw [entrySum_cons, entrySum_zero_of_not_mem es a.row a.column hnodup.1]
        simp
      · have hne : ¬(a.row = e.row ∧ a.column = e.column) := by
          intro hh
          apply hnodup.1
          exact List.mem_map.mpr ⟨e, he, (Prod.ext hh.1 hh.2).symm⟩
        rw [entrySum_cons, ite_eq_right hne, zero_add]
        exact ih hnodup.2 he

theorem entrySum_nonzero_iff (es : List Entry) (hn : (es.map Entry.key).Nodup)
    (hv : ∀ e ∈ es, e.value ≠ 0) (i j : ℕ) :
    entrySum es i j ≠ 0 ↔ (i, j) ∈ es.map Entry.key := by
  constructor
  · intro h
    by_contra h'
    exact h (entrySum_zero_of_not_mem es i j h')
  · intro h
    obtain ⟨e, he, hk⟩ := List.mem_map.mp h
    have hr := congrArg Prod.fst hk
    have hc := congrArg Prod.snd hk
    change e.row = i at hr
    change e.column = j at hc
    rw [← hr, ← hc, entrySum_at_entry es hn e he]
    exact hv e he

end Maxwell.Logical.RationalCode
