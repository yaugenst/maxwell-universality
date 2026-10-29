import Maxwell.Cost.RealSparseOrder.RelabelRecord

namespace Maxwell.Cost.RealSparseOrder.Relabel
open RealSimulation.Control

/-- A full in-place relabel and addressed RHS gather. Its map has one entry
per consecutive row group and the scan pays at most twenty-one instructions
per input record, including every loop test. -/
theorem executes (input : RAMInput) (tape : ℕ→Bool) (vector : ℕ→ℝ)
    (s : Store) (b : Buffer) (es : List SparseEntry) (previous : Option ℕ)
    (count m map rhs : ℕ)
    (h : Config s.val b es.length previous count m map rhs)
    (hb : b.Safe) (hm : b.coordinates+2*es.length≤map)
    (hv : b.coefficients+es.length≤rhs) (hs : Records b s.val es)
    (hin : ∀row,input.words (m+row)=vector row) :
    ∃cost t,cost≤21*es.length+1 ∧Executes input tape loopCode cost s t ∧
      Config t.val (b.shift es.length) 0 (lastRow previous es)
        (count+(retained previous es).length) m map rhs ∧
      Records b t.val (relabeled previous count es) ∧
      Gathered (map+count) (rhs+count) t.val vector (retained previous es) ∧
      Frame b es.length map rhs count s.val t.val ∧
      t.val.randomCursor=s.val.randomCursor ∧t.val.output=s.val.output ∧
      t.val.indexOutput=s.val.indexOutput := by
  induction es generalizing s b previous count with
  | nil =>
    refine ⟨1,s,by simp,?_,?_,trivial,trivial,Frame.refl _ _ _ _ _ _,rfl,rfl,rfl⟩
    · exact Executes.done (by rw [h.one,h.remaining]; simp)
    · simpa [lastRow,retained] using h
  | cons e es ih =>
    have hmap : 100≤map := by have hh:=hb.2; simp only [List.length_cons] at hm; omega
    have hrhs : 100≤rhs := by have hh:=hb.1; simp only [List.length_cons] at hv; omega
    let mid := processed input previous e.row s
    let c := nextCount previous count e.row
    have hc : Config mid.val (b.shift 1) es.length (some e.row) c m map rhs := by
      simpa only [List.length_cons,Nat.add_sub_cancel] using processed_config h hb.2 hmap hs.1
    have hmrecords := processed_records h hb hm hv hs (input:=input)
    have hmlayout : (b.shift 1).coordinates+2*es.length≤map := by
      simp only [Buffer.shift,List.length_cons] at *; omega
    have hvlayout : (b.shift 1).coefficients+es.length≤rhs := by
      simp only [Buffer.shift,List.length_cons] at *; omega
    obtain ⟨first,hfirst,firstRun⟩ := step input tape s b (e::es).length previous count m map rhs
      e.row h hb.2 hmap hrhs hs.1
    obtain ⟨rest,t,hrest,tailRun,hfinal,hrecords,hgather,hframe,hcursor,houtput,hindex⟩ :=
      ih mid (b.shift 1) (some e.row) c hc (hb.shift 1) hmlayout hvlayout hmrecords.2.2.2
    have hcl : count≤c := by dsimp [c,nextCount]; split <;> omega
    have hcu : c≤count+1 := by dsimp [c,nextCount]; split <;> omega
    have hheadrow : t.val.indices b.coordinates=nextCount previous count e.row-1 :=
      (hframe.1 b.coordinates hb.2
        (by simp only [Buffer.shift]; left; omega) (by left; simp only [List.length_cons] at hm; omega)).trans
        hmrecords.1
    have hheadcolumn : t.val.indices (b.coordinates+1)=e.column :=
      (hframe.1 (b.coordinates+1) (by have hh:=hb.2; omega)
        (by simp only [Buffer.shift]; left; omega) (by left; simp only [List.length_cons] at hm; omega)).trans
        hmrecords.2.1
    have hheadvalue : t.val.words b.coefficients=e.value :=
      (hframe.2 b.coefficients (by have hh:=hb.1; omega)
        (by left; simp only [List.length_cons] at hv; omega)).trans hmrecords.2.2.1
    refine ⟨1+first+rest,t,by simp only [List.length_cons]; omega,
      Executes.more (by rw [h.one,h.remaining]; simp) firstRun tailRun,?_,
      ⟨hheadrow,hheadcolumn,hheadvalue,hrecords⟩,?_,?_,?_,?_,?_⟩
    · have hcount := retained_count previous count e es
      have hshift : (b.shift 1).shift es.length=b.shift (e::es).length := by
        simp [Buffer.shift_shift,Nat.add_comm]
      rw [hshift] at hfinal
      change Config t.val (b.shift (e::es).length) 0 (lastRow (some e.row) es)
        (count+(retained previous (e::es)).length) m map rhs
      simpa only [c,hcount] using hfinal
    · by_cases he : previous=some e.row
      · simpa only [retained,he,ite_true,c,nextCount] using hgather
      · have hcnew : c=count+1 := by simp [c,nextCount,he]
        have hghead := processed_gathered vector h hb (by simp only [List.length_cons] at hm; omega)
          hrhs hs.1 he (hin e.row) (input:=input)
        have hmi : t.val.indices (map+count)=e.row :=
          (hframe.1 (map+count) (by omega)
            (by right; simp only [Buffer.shift]; simp only [List.length_cons] at hm; omega)
            (by left; omega)).trans hghead.1
        have hmv : t.val.words (rhs+count)=vector e.row :=
          (hframe.2 (rhs+count) (by omega) (by left; omega)).trans hghead.2.1
        rw [retained,ite_eq_right he]
        refine ⟨hmi,hmv,?_⟩
        simpa only [hcnew,Nat.add_assoc] using hgather
    · exact ((processed_frame h hmap hs.1).mono (by simp)).trans (hframe.tail hcl hcu)
    · exact hcursor.trans (processed_channels input previous e.row s).1
    · exact houtput.trans (processed_channels input previous e.row s).2.1
    · exact hindex.trans (processed_channels input previous e.row s).2.2

end Maxwell.Cost.RealSparseOrder.Relabel
