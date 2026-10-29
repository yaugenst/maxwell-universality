import Maxwell.Cost.RealSparseOrder.ColumnMaxState

namespace Maxwell.Cost.RealSparseOrder.ColumnMax
open RealSimulation.Control RealSimulation.IndexWidth

/-- The scan visits every stored column through an addressed load. Its fixed
boundary bound is restored after every record. -/
theorem bounded_loop (input : RAMInput) (tape : ℕ→Bool) (B : ℕ)
    (s : Store) (b : Buffer) (es : List SparseEntry) (acc : ℕ)
    (h : Config s.val b es.length acc) (hb : b.Safe) (hr : Records b s.val es)
    (hs : IndexBound B s.val) (hc : b.coordinates+2*es.length+1≤B)
    (hcols : ∀e∈es,e.column+1≤B) :
    ∃cost t,cost≤10*es.length+1 ∧BoundedExecutes B 9 input tape loopCode cost s t ∧
      Config t.val (b.shift es.length) 0 (max acc (columnCount es)) ∧
      (∀j,j<42 ∨46≤j→t.val.indices j=s.val.indices j) ∧t.val.words=s.val.words ∧
      t.val.randomCursor=s.val.randomCursor ∧t.val.output=s.val.output ∧
      t.val.indexOutput=s.val.indexOutput := by
  induction es generalizing s b acc with
  | nil =>
    refine ⟨1,s,by simp,BoundedExecutes.done (by rw [h.one,h.remaining]; simp) hs,
      ?_,?_,rfl,rfl,rfl,rfl⟩
    · simpa [columnCount] using h
    · intro j _; rfl
  | cons e es ih =>
    let mid := processed s
    have hmid : Config mid.val (b.shift 1) es.length (max acc (e.column+1)) := by
      simpa only [List.length_cons,Nat.add_sub_cancel] using processed_config h hr.2.1
    have hbound : IndexBound B mid.val := processed_index_bound hs
      (by rw [h.cursor,hr.2.1]; exact hcols e (by simp))
      (by rw [h.cursor]; simp only [List.length_cons] at hc; omega)
    obtain ⟨first,hfirst,firstRun⟩ := step input tape s h.one h.two
    obtain ⟨rest,t,hrest,tailRun,hfinal,hframe,hwords,hcursor,houtput,hindex⟩ :=
      ih mid (b.shift 1) (max acc (e.column+1)) hmid (hb.shift 1)
        (records_processed hr hb).2.2.2 hbound
        (by simp only [Buffer.shift,List.length_cons] at *; omega)
        (fun f hf=>hcols f (by simp [hf]))
    refine ⟨1+first+rest,t,by simp only [List.length_cons]; omega,
      BoundedExecutes.more (by rw [h.one,h.remaining]; simp)
        (BoundedExecutes.atom firstRun hfirst hs hbound) tailRun,?_,?_,?_,?_,?_,?_⟩
    · simpa only [Buffer.shift_shift,List.length_cons,Nat.add_comm 1 es.length,
        columnCount,max_assoc] using hfinal
    · intro j hj
      exact (hframe j hj).trans (processed_frame s j hj)
    · exact hwords.trans (processed_words s)
    · exact hcursor.trans (processed_channels s).1
    · exact houtput.trans (processed_channels s).2.1
    · exact hindex.trans (processed_channels s).2.2

end Maxwell.Cost.RealSparseOrder.ColumnMax
