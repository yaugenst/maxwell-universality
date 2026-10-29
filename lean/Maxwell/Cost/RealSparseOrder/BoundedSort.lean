import Maxwell.Cost.RealSparseOrder.BoundedPassLoop
import Maxwell.Cost.RealSparseOrder.SortLoop

namespace Maxwell.Cost.RealSparseOrder.Sort
open RealSimulation.Control RealSimulation.IndexWidth

structure Bounded (B : ℕ) (s : RAMState) (src dst : Buffer) (width : ℕ)
    (runs : List (List SparseEntry)) : Prop where
  invariant : Invariant s src dst width runs
  indices : IndexBound B s
  sourceEnd : Within B src runs.flatten.length
  targetEnd : Within B dst runs.flatten.length
  size : 2*runs.flatten.length≤B

theorem bounded_step (input : RAMInput) (tape : ℕ→Bool) (B : ℕ) (s : Store)
    (src dst : Buffer) (width : ℕ) (runs : List (List SparseEntry))
    (hw : 0<width) (hp : PackedRuns width runs)
    (h : Bounded B s.val src dst width runs) (hwidth : 2*width≤B) :
    ∃cost t, BoundedExecutes B 30 input tape stepCode cost s t := by
  let start := Store.ofState (OuterControl.prepared s.val)
  have hs : Pass.Bounded B start.val src dst width runs.flatten := by
    apply (Pass.bounded_ofState _ _ _ _ _ _).mpr
    exact ⟨h.invariant.prepared,outerPrepare_index_bound h.indices,h.sourceEnd,h.targetEnd,h.size⟩
  obtain ⟨cost,mid,_,run,cfg,_,_,_,_⟩ :=
    Pass.executes input tape start src dst width runs hw hp hs.invariant
  have bounded := Pass.bound_execution input tape B start src dst width runs hw hp hs run
  have finish : IndexBound B (OuterControl.advanced mid.val) :=
    outerAdvance_index_bound bounded.finish (by rw [cfg.width]; exact hwidth)
  exact ⟨6+(cost+8),Store.ofState (OuterControl.advanced mid.val),
    BoundedExecutes.seq (.atom (OuterControl.prepare_executes input tape s) (by omega) h.indices hs.indices)
      (.seq bounded (.atom (OuterControl.advance_executes input tape mid) (by omega) bounded.finish finish))⟩

theorem bound_step_execution (input : RAMInput) (tape : ℕ→Bool) (B : ℕ) (s : Store)
    (src dst : Buffer) (width : ℕ) (runs : List (List SparseEntry))
    (hw : 0<width) (hp : PackedRuns width runs)
    (h : Bounded B s.val src dst width runs) (hwidth : 2*width≤B)
    {cost : ℕ} {t : Store} (run : Executes input tape stepCode cost s t) :
    BoundedExecutes B 30 input tape stepCode cost s t := by
  obtain ⟨other,u,bounded⟩ := bounded_step input tape B s src dst width runs hw hp h hwidth
  obtain ⟨rfl,rfl⟩ := run.deterministic bounded.executes
  exact bounded

private theorem bounded_loop_passes (input : RAMInput) (tape : ℕ→Bool) (B k j : ℕ)
    (s : Store) (src dst : Buffer) (runs : List (List SparseEntry))
    (h : Bounded B s.val src dst (2^j) runs) (hp : PackedRuns (2^j) runs)
    (hk : j+k=runs.flatten.length.size) :
    ∃cost t, BoundedExecutes B 30 input tape loopCode cost s t := by
  induction k generalizing j s src dst runs with
  | zero =>
    refine ⟨1,s,BoundedExecutes.done ?_ h.indices⟩
    rw [h.invariant.config.width,h.invariant.config.count]
    have he : j=runs.flatten.length.size := by omega
    rw [he]
    exact Nat.not_le.mpr (Nat.lt_size_self _)
  | succ k ih =>
    have hj : j<runs.flatten.length.size := by omega
    have hsmall : 2^j≤runs.flatten.length := Nat.lt_size.mp hj
    have test : s.val.indices 18≤s.val.indices 26 := by
      rw [h.invariant.config.width,h.invariant.config.count]
      exact hsmall
    obtain ⟨first,mid,_,run,hi,_,_⟩ := step input tape s src dst (2^j) runs (by positivity) hp h.invariant
    have bounded := bound_step_execution input tape B s src dst (2^j) runs (by positivity) hp h
      (by have hh := h.size; omega) run
    have hb : Bounded B mid.val dst src (2^(j+1)) (mergePass runs) := by
      refine ⟨?_,bounded.finish,?_,?_,?_⟩
      · simpa only [pow_succ,Nat.mul_comm] using hi
      · simpa only [mergePass_mass] using h.targetEnd
      · simpa only [mergePass_mass] using h.sourceEnd
      · simpa only [mergePass_mass] using h.size
    have hp' : PackedRuns (2^(j+1)) (mergePass runs) := by
      simpa only [pow_succ,Nat.mul_comm] using mergePass_packed (2^j) runs hp
    have hk' : (j+1)+k=(mergePass runs).flatten.length.size := by rw [mergePass_mass]; omega
    obtain ⟨cost,t,tailRun⟩ := ih (j+1) mid dst src (mergePass runs) hb hp' hk'
    exact ⟨1+first+cost,t,BoundedExecutes.more test bounded tailRun⟩

/-- A complete sort has a constant macro-length word overhead, independently
of its number of records and passes. -/
theorem bounded_loop (input : RAMInput) (tape : ℕ→Bool) (B : ℕ) (s : Store)
    (src dst : Buffer) (entries : List SparseEntry)
    (h : Bounded B s.val src dst 1 (singletonRuns entries)) :
    ∃cost t, BoundedExecutes B 30 input tape loopCode cost s t :=
  bounded_loop_passes input tape B entries.length.size 0 s src dst (singletonRuns entries)
    (by simpa using h) (by simpa using singletonRuns_packed entries) (by simp)

theorem bound_execution (input : RAMInput) (tape : ℕ→Bool) (B : ℕ) (s : Store)
    (src dst : Buffer) (entries : List SparseEntry)
    (h : Bounded B s.val src dst 1 (singletonRuns entries))
    {cost : ℕ} {t : Store} (run : Executes input tape loopCode cost s t) :
    BoundedExecutes B 30 input tape loopCode cost s t := by
  obtain ⟨other,u,bounded⟩ := bounded_loop input tape B s src dst entries h
  obtain ⟨rfl,rfl⟩ := run.deterministic bounded.executes
  exact bounded

end Maxwell.Cost.RealSparseOrder.Sort
