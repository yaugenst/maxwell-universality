import Maxwell.Cost.RealSparseOrder.RelabelPure

namespace Maxwell.Cost.RealSparseOrder.Relabel

private theorem retained_gt (bound : ℕ) (es : List SparseEntry)
    (hs : es.Pairwise KeyLE) (hb : ∀e∈es,bound≤e.row) :
    ∀r∈retained (some bound) es,bound<r := by
  induction es generalizing bound with
  | nil => simp [retained]
  | cons e es ih =>
    obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hs
    have he := hb e (by simp)
    by_cases hh : bound=e.row
    · simp only [retained,hh,ite_true]
      exact ih e.row htail (fun f hf=>by simpa only [←hh] using hb f (by simp [hf]))
    · intro r hr
      simp only [retained,Option.some.injEq,hh,ite_false,List.mem_cons] at hr
      rcases hr with hr|hr
      · omega
      · obtain ⟨f,hf,hfr⟩ := retained_mem hr
        have horder := hhead f hf
        unfold KeyLE at horder
        omega

/-- On sorted input the retained labels are strictly increasing, so the
map contains each active original row exactly once. -/
theorem retained_strict (previous : Option ℕ) (es : List SparseEntry)
    (hs : es.Pairwise KeyLE) : (retained previous es).Pairwise (·<·) := by
  induction es generalizing previous with
  | nil => simp [retained]
  | cons e es ih =>
    obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hs
    by_cases hh : previous=some e.row
    · simpa only [retained,hh,ite_true] using ih (some e.row) htail
    · simp only [retained,hh,ite_false,List.pairwise_cons]
      refine ⟨retained_gt e.row es htail ?_,ih (some e.row) htail⟩
      intro f hf
      have h := hhead f hf
      unfold KeyLE at h
      omega

/-- Replacing every new rank by its retained original label recovers each
record's row; columns and real coefficients are preserved in order. -/
theorem relabeled_recovery (history : List ℕ) (es : List SparseEntry) :
    List.Forall₂ (fun old new=>
      (history++retained history.getLast? es)[new.row]?=some old.row ∧
        new.column=old.column ∧new.value=old.value)
      es (relabeled history.getLast? history.length es) := by
  induction es generalizing history with
  | nil => exact .nil
  | cons e es ih =>
    by_cases hh : history.getLast?=some e.row
    · have hn : 0<history.length := by
        by_contra h
        have he : history=[] := List.length_eq_zero_iff.mp (by omega)
        simp [he] at hh
      simp only [relabeled,nextCount,hh,ite_true,retained]
      refine List.Forall₂.cons ⟨?_,rfl,rfl⟩ ?_
      · change (history++retained (some e.row) es)[history.length-1]?=some e.row
        rw [List.getElem?_append_left (by omega),←List.getLast?_eq_getElem?,hh]
      · simpa only [hh] using ih history
    · let h := history++[e.row]
      have hl : h.length=history.length+1 := by simp [h]
      have hp : h.getLast?=some e.row := by simp [h]
      have he : history++retained history.getLast? (e::es)=h++retained (some e.row) es := by
        simp [retained,hh,h,List.append_assoc]
      change List.Forall₂ _ (e::es)
        ({e with row:=nextCount history.getLast? history.length e.row-1}::
          relabeled (some e.row) (nextCount history.getLast? history.length e.row) es)
      simp only [nextCount,hh,ite_false]
      refine List.Forall₂.cons ⟨?_,rfl,rfl⟩ ?_
      · rw [he]
        simp [h,List.append_assoc]
      · have ht := ih h
        rw [hp,hl] at ht
        simpa only [he] using ht

theorem initial_recovery (es : List SparseEntry) :
    List.Forall₂ (fun old new=>(retained none es)[new.row]?=some old.row ∧
      new.column=old.column ∧new.value=old.value) es (relabeled none 0 es) := by
  simpa using relabeled_recovery [] es

theorem relabeled_new_rank (previous : Option ℕ) (count : ℕ) (es : List SparseEntry) :
    ∀k,count≤k→k<count+(retained previous es).length→
      ∃e∈relabeled previous count es,e.row=k := by
  induction es generalizing previous count with
  | nil => simp [retained]; omega
  | cons e es ih =>
    intro k hlow hhigh
    by_cases he : previous=some e.row
    · have hh : k<count+(retained (some e.row) es).length := by
        simpa only [retained,he,ite_true] using hhigh
      obtain ⟨f,hf,hrow⟩ := ih (some e.row) count k hlow hh
      exact ⟨f,by simp [relabeled,nextCount,he,hf],hrow⟩
    · by_cases hk : k=count
      · subst k
        exact ⟨{e with row:=count},by simp [relabeled,nextCount,he],rfl⟩
      · have hh : k<(count+1)+(retained (some e.row) es).length := by
          simp only [retained,he,ite_false,List.length_cons] at hhigh
          omega
        obtain ⟨f,hf,hrow⟩ := ih (some e.row) (count+1) k (by omega) hh
        exact ⟨f,by simp [relabeled,nextCount,he,hf],hrow⟩

theorem initial_rank_surjective (es : List SparseEntry) (k : ℕ) (hk : k<(retained none es).length) :
    ∃e∈relabeled none 0 es,e.row=k :=
  relabeled_new_rank none 0 es k (Nat.zero_le _) (by simpa using hk)

end Maxwell.Cost.RealSparseOrder.Relabel
