import Maxwell.Cost.RealSparseOrder.PassState

namespace Maxwell.Cost.RealSparseOrder.Pass
open RealSimulation.Control

def blockCode : Code := .seq Merge.loopCode (.call PassAdvance.program)

def ControlFrame (s t : RAMState) : Prop :=
  ∀j,26≤j → j<100 → t.indices j=s.indices j

/-- A prepared adjacent-run merge followed by its actual descriptor update. -/
theorem block (input : RAMInput) (tape : ℕ→Bool) (s : Store)
    (src dst : Buffer) (width : ℕ) (xs ys rest : List SparseEntry)
    (h : Invariant s.val src dst width (xs++ys++rest))
    (cfg : Merge.Config s.val src xs.length (src.shift xs.length) ys.length dst)
    (hc : s.val.indices 24=xs.length+ys.length)
    (hc2 : s.val.indices 25=2*(xs.length+ys.length)) :
    ∃cost t, cost≤28*(xs.length+ys.length)+7 ∧
      Executes input tape blockCode cost s t ∧
      Invariant t.val (src.shift (xs.length+ys.length))
        (dst.shift (xs.length+ys.length)) width rest ∧
      Records dst t.val (merge xs ys) ∧
      DataFrame dst (xs.length+ys.length) s.val t.val ∧
      ControlFrame s.val t.val ∧Merge.Channels s.val t.val := by
  have hsrc : Records src s.val (xs++(ys++rest)) := by simpa only [List.append_assoc] using h.records
  rcases (records_append src s.val xs (ys++rest)).mp hsrc with ⟨hxs,htail⟩
  rcases (records_append (src.shift xs.length) s.val ys rest).mp htail with ⟨hys,hr⟩
  have hrest : Records (src.shift (xs.length+ys.length)) s.val rest := by
    simpa only [Buffer.shift_shift] using hr
  have mi : Merge.Invariant s.val src (src.shift xs.length) dst xs ys := by
    refine ⟨cfg,h.safeSource,h.safeSource.shift _,h.safeTarget,hxs,hys,?_,?_⟩
    · simpa using h.separated.subset (i:=0) (r:=xs.length) (j:=0) (q:=xs.length+ys.length)
        (by simp) (by simp)
    · simpa using h.separated.subset (i:=xs.length) (r:=ys.length) (j:=0) (q:=xs.length+ys.length)
        (by simp) (by simp)
  obtain ⟨cost,mid,af,bf,hcost,run,mcfg,merged,frame,channels⟩ :=
    Merge.executes input tape s src (src.shift xs.length) dst xs ys mi
  have hmeta (j : ℕ) (hlo : 17≤j) (hhi : j<100) : mid.val.indices j=s.val.indices j :=
    frame.1 j hlo (Or.inl (by have hh := h.safeTarget.2; omega))
  have pcfg := h.config.after_merge h.safeTarget frame mcfg.zero mcfg.one mcfg.two
  have hc' : mid.val.indices 24=xs.length+ys.length := (hmeta 24 (by omega) (by omega)).trans hc
  have hc2' : mid.val.indices 25=2*(xs.length+ys.length) := (hmeta 25 (by omega) (by omega)).trans hc2
  have precords : Records (src.shift (xs.length+ys.length)) mid.val rest := by
    apply hrest.frame (h.safeSource.shift _) _ frame
    simpa using h.separated.subset (i:=xs.length+ys.length) (r:=rest.length)
      (j:=0) (q:=xs.length+ys.length) (by simp [Nat.add_assoc]) (by simp)
  let t := Store.ofState (PassAdvance.advanced mid.val)
  have hfinal : Invariant t.val (src.shift (xs.length+ys.length))
      (dst.shift (xs.length+ys.length)) width rest := by
    apply (invariant_ofState _ _ _ _ _).mpr
    refine ⟨?_,h.safeSource.shift _,h.safeTarget.shift _,
      records_advance precords (h.safeSource.shift _),?_⟩
    · simpa only [List.length_append,Nat.add_sub_cancel_left] using pcfg.advance hc' hc2'
    · exact h.separated.subset (i:=xs.length+ys.length) (r:=rest.length)
        (j:=xs.length+ys.length) (q:=rest.length) (by simp [Nat.add_assoc]) (by simp [Nat.add_assoc])
  refine ⟨cost+6,t,by omega,Executes.seq run (PassAdvance.executes input tape mid),hfinal,?_,?_,?_,?_⟩
  · exact (Merge.records_ofState _ _ _).mpr (records_advance merged h.safeTarget)
  · exact frame.dataFrame.trans ((PassAdvance.data_frame mid.val dst).mono (by omega))
  · intro j hj hk
    exact (PassAdvance.indices_frame mid.val j (Or.inr hj)).trans (hmeta j (by omega) hk)
  · exact channels

end Maxwell.Cost.RealSparseOrder.Pass
