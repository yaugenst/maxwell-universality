import Maxwell.Cost.RealSparseOrder.PassStep
import Maxwell.Cost.RealSparseOrder.MergePass

namespace Maxwell.Cost.RealSparseOrder.Pass
open RealSimulation.Control

/-- The physical loop agrees with the packed adjacent-run pass. The ghost
run boundaries justify the actual minimum arithmetic; they are not inputs
to the finite program. -/
theorem executes (input : RAMInput) (tape : ℕ→Bool) (s : Store)
    (src dst : Buffer) (width : ℕ) (runs : List (List SparseEntry))
    (hw : 0<width) (hp : PackedRuns width runs)
    (h : Invariant s.val src dst width runs.flatten) :
    ∃cost t, cost≤54*mergePassWork runs+1 ∧Executes input tape loopCode cost s t ∧
      Config t.val (src.shift runs.flatten.length) (dst.shift runs.flatten.length) width 0 ∧
      Records dst t.val (mergePass runs).flatten ∧
      DataFrame dst runs.flatten.length s.val t.val ∧
      ControlFrame s.val t.val ∧Merge.Channels s.val t.val := by
  induction runs using List.twoStepInduction generalizing s src dst with
  | nil =>
    refine ⟨1,s,by simp [mergePassWork],?_,?_,?_,DataFrame.refl _ _ _,?_,⟨rfl,rfl,rfl⟩⟩
    · exact Executes.done (by rw [h.config.one,h.config.remaining]; simp)
    · simpa using h.config
    · simp
    · intro _ _ _; rfl
  | singleton a =>
    by_cases he : a=[]
    · subst a
      refine ⟨1,s,by simp [mergePassWork],?_,?_,?_,DataFrame.refl _ _ _,?_,⟨rfl,rfl,rfl⟩⟩
      · exact Executes.done (by rw [h.config.one,h.config.remaining]; simp)
      · simpa using h.config
      · simp
      · intro _ _ _; rfl
    · have ha : 0<a.length := List.length_pos_iff.mpr he
      have hh : Invariant s.val src dst width (a++[]++[]) := by simpa using h
      obtain ⟨cost,t,hcost,run,hi,records,frame,control,channels⟩ :=
        step input tape s src dst width a [] [] hh
          (by simpa using (min_eq_right hp.1).symm) (by simp)
      refine ⟨1+cost+1,t,?_,?_,?_,?_,?_,control,channels⟩
      · simp only [mergePassWork] at *
        simp only [List.length_nil,Nat.add_zero] at hcost
        omega
      · have test : s.val.indices 1≤s.val.indices 17 := by
          rw [h.config.one,h.config.remaining]
          simp only [List.flatten_cons,List.flatten_nil,List.append_nil]
          omega
        exact Executes.more test run
          (Executes.done (by rw [hi.config.one,hi.config.remaining]; simp))
      · simpa using hi.config
      · simpa [merge] using records
      · simpa using frame
  | cons_cons a b rest ih _ =>
    have hapos : 0<a.length := by rw [hp.2.1 (by simp)]; exact hw
    have hflat : (a::b::rest).flatten=a++b++rest.flatten := by simp [List.append_assoc]
    have hh : Invariant s.val src dst width (a++b++rest.flatten) := by simpa only [hflat] using h
    have hleft : a.length=min width (a++b++rest.flatten).length := by
      have ht := congrArg List.length (packed_pair_slices width a b rest hp).1
      simpa only [List.length_take,hflat] using ht.symm
    have hright : b.length=min width ((a++b++rest.flatten).length-a.length) := by
      have ht := congrArg List.length (packed_pair_slices width a b rest hp).2.1
      have hafull := hp.2.1 (by simp)
      simpa only [List.length_take,List.length_drop,hflat,hafull] using ht.symm
    obtain ⟨first,mid,hfirst,run,hi,records,frame,control,channels⟩ :=
      step input tape s src dst width a b rest.flatten hh hleft hright
    obtain ⟨cost,t,hcost,tailRun,cfg,tailRecords,tailFrame,tailControl,tailChannels⟩ :=
      ih mid (src.shift (a.length+b.length)) (dst.shift (a.length+b.length)) hp.2.2.2.2 hi
    have kept : Records dst t.val (merge a b) := records.dataFrame h.safeTarget (by
      simp only [Separated,Buffer.shift,merge_length]
      constructor <;> left <;> omega) tailFrame
    refine ⟨1+first+cost,t,?_,?_,?_,?_,?_,?_,?_⟩
    · simp only [mergePassWork]
      omega
    · have test : s.val.indices 1≤s.val.indices 17 := by
        rw [h.config.one,h.config.remaining,hflat]
        simp only [List.length_append]
        omega
      exact Executes.more test run tailRun
    · simpa only [Buffer.shift_shift,hflat,List.length_append] using cfg
    · change Records dst t.val (merge a b++(mergePass rest).flatten)
      apply (records_append _ _ _ _).mpr
      exact ⟨kept,by simpa only [merge_length] using tailRecords⟩
    · have heq : (a::b::rest).flatten.length=a.length+b.length+rest.flatten.length := by
        simp only [hflat,List.length_append]
      rw [heq]
      exact (frame.mono (by omega)).trans tailFrame.shift_subset
    · intro j hj hk
      exact (tailControl j hj hk).trans (control j hj hk)
    · exact ⟨tailChannels.1.trans channels.1,tailChannels.2.1.trans channels.2.1,
        tailChannels.2.2.trans channels.2.2⟩

end Maxwell.Cost.RealSparseOrder.Pass
