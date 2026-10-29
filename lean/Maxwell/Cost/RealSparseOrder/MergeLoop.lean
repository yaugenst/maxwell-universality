import Maxwell.Cost.RealSparseOrder.MergeStep

namespace Maxwell.Cost.RealSparseOrder.Merge
open RealSimulation.Control

private theorem loop_of_length (input : RAMInput) (tape : ℕ→Bool) (N : ℕ)
    (s : Store) (a b out : Buffer) (xs ys : List SparseEntry)
    (h : Invariant s.val a b out xs ys) (hlen : xs.length+ys.length=N) :
    ∃cost t af bf, cost≤28*N+1 ∧Executes input tape loopCode cost s t ∧
      Config t.val af 0 bf 0 (out.shift N) ∧Records out t.val (merge xs ys) ∧
      MemoryFrame out N s.val t.val ∧Channels s.val t.val := by
  induction N using Nat.strong_induction_on generalizing s a b out xs ys with
  | h N ih =>
    by_cases hn : N=0
    · have hx : xs=[] := List.length_eq_zero_iff.mp (by omega)
      have hy : ys=[] := List.length_eq_zero_iff.mp (by omega)
      subst xs; subst ys; subst N
      refine ⟨1,s,a,b,by omega,?_,?_,?_,MemoryFrame.refl _ _ _,⟨rfl,rfl,rfl⟩⟩
      · exact Executes.done (by rw [h.config.one,h.config.total]; simp)
      · simpa using h.config
      · simp [merge]
    · obtain ⟨first,mid,e,xs',ys',a',b',hcost,run,step⟩ :=
        Merge.step input tape s a b out xs ys h (by omega)
      have hslen := step.length
      let R := xs'.length+ys'.length
      have hR : R<N := by dsimp [R]; omega
      obtain ⟨rest,t,af,bf,hrest,tailRun,hfinal,hrecords,hframe,hchannels⟩ :=
        ih R hR mid a' b' (out.shift 1) xs' ys' step.invariant rfl
      have hhead : Records out t.val [e] := step.head.frame h.safeOut
        (by simp only [Separated,Buffer.shift,List.length_singleton]; constructor <;> left <;> omega)
        hframe
      refine ⟨1+first+rest,t,af,bf,by dsimp [R] at *; omega,
        Executes.more (by rw [h.config.one,h.config.total]; omega) run tailRun,?_,?_,?_,?_⟩
      · have heq : 1+R=N := by dsimp [R]; omega
        simpa only [Buffer.shift_shift,heq] using hfinal
      · rw [step.merge_eq]
        exact ⟨hhead.1,hhead.2.1,hhead.2.2.1,hrecords⟩
      · have heq : 1+R=N := by dsimp [R]; omega
        exact (step.frame.mono (by omega)).trans (by
          simpa only [heq] using hframe.shift_subset)
      · exact ⟨hchannels.1.trans step.channels.1,hchannels.2.1.trans step.channels.2.1,
          hchannels.2.2.trans step.channels.2.2⟩

/-- A fixed finite addressed merge performs at most twenty-eight instructions
per output record. The result includes all memory outside the destination
interval, not just the named source arrays. -/
theorem executes (input : RAMInput) (tape : ℕ→Bool)
    (s : Store) (a b out : Buffer) (xs ys : List SparseEntry)
    (h : Invariant s.val a b out xs ys) :
    ∃cost t af bf, cost≤28*(xs.length+ys.length)+1 ∧
      Executes input tape loopCode cost s t ∧
      Config t.val af 0 bf 0 (out.shift (xs.length+ys.length)) ∧
      Records out t.val (merge xs ys) ∧
      MemoryFrame out (xs.length+ys.length) s.val t.val ∧Channels s.val t.val :=
  loop_of_length input tape _ s a b out xs ys h rfl

theorem run (input : RAMInput) (tape : ℕ→Bool)
    (s : Store) (a b out : Buffer) (xs ys : List SparseEntry)
    (h : Invariant s.val a b out xs ys) :
    ∃(cost : ℕ) (t : Store), cost≤28*(xs.length+ys.length)+1 ∧
      (runCapped (loopCode.compile.next input tape)
        (28*(xs.length+ys.length)+2) s.val).finished=some (t.place loopCode.size) ∧
      (runCapped (loopCode.compile.next input tape)
        (28*(xs.length+ys.length)+2) s.val).instructions=cost ∧
      Records out t.val (merge xs ys) := by
  obtain ⟨cost,t,_,_,hc,hr,_,hs,_⟩ := executes input tape s a b out xs ys h
  have run := hr.compiled_run (28*(xs.length+ys.length)+2) (by omega)
  exact ⟨cost,t,hc,run.1,run.2,hs⟩

end Maxwell.Cost.RealSparseOrder.Merge
