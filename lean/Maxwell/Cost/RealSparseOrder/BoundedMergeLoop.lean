import Maxwell.Cost.RealSparseOrder.BoundedMerge
import Maxwell.Cost.RealSimulation.ControlBounds

namespace Maxwell.Cost.RealSparseOrder.Merge
open RealSimulation.Control RealSimulation.IndexWidth

private theorem bounded_loop_length (input : RAMInput) (tape : ℕ→Bool) (B N : ℕ)
    (s : Store) (a b out : Buffer) (xs ys : List SparseEntry)
    (h : Bounded B s.val a b out xs ys) (hlen : xs.length+ys.length=N) :
    ∃cost t, BoundedExecutes B 30 input tape loopCode cost s t := by
  induction N using Nat.strong_induction_on generalizing s a b out xs ys with
  | h N ih =>
    by_cases hn : N=0
    · refine ⟨1,s,BoundedExecutes.done ?_ h.indices⟩
      rw [h.invariant.config.one,h.invariant.config.total]
      omega
    · obtain ⟨first,mid,xs',ys',a',b',hcost,run,hsize,hm⟩ :=
        bounded_step input tape B s a b out xs ys h (by omega)
      obtain ⟨rest,t,tailRun⟩ := ih (xs'.length+ys'.length) (by omega)
        mid a' b' (out.shift 1) xs' ys' hm rfl
      have test : s.val.indices 1≤s.val.indices 5 := by
        rw [h.invariant.config.one,h.invariant.config.total]
        omega
      exact ⟨1+first+rest,t,BoundedExecutes.more test
        (.atom run (by omega) h.indices hm.indices) tailRun⟩

/-- The number of records never appears in the inflation exponent: every
actual merge body returns to the original global index cap. -/
theorem bounded_loop (input : RAMInput) (tape : ℕ→Bool) (B : ℕ)
    (s : Store) (a b out : Buffer) (xs ys : List SparseEntry)
    (h : Bounded B s.val a b out xs ys) :
    ∃cost t, BoundedExecutes B 30 input tape loopCode cost s t :=
  bounded_loop_length input tape B _ s a b out xs ys h rfl

end Maxwell.Cost.RealSparseOrder.Merge
