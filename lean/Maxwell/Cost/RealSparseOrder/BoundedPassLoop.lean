import Maxwell.Cost.RealSparseOrder.BoundedPass
import Maxwell.Cost.RealSparseOrder.PassLoop

namespace Maxwell.Cost.RealSparseOrder.Pass
open RealSimulation.Control RealSimulation.IndexWidth

theorem bound_step_execution (input : RAMInput) (tape : ℕ→Bool) (B : ℕ) (s : Store)
    (src dst : Buffer) (width : ℕ) (xs ys rest : List SparseEntry)
    (h : Bounded B s.val src dst width (xs++ys++rest))
    (hl : xs.length=min width (xs++ys++rest).length)
    (hr : ys.length=min width ((xs++ys++rest).length-xs.length))
    {cost : ℕ} {t : Store} (run : Executes input tape stepCode cost s t) :
    BoundedExecutes B 30 input tape stepCode cost s t := by
  obtain ⟨other,u,bounded⟩ := bounded_step input tape B s src dst width xs ys rest h hl hr
  obtain ⟨rfl,rfl⟩ := run.deterministic bounded.executes
  exact bounded

/-- The entire addressed pass preserves the cap at every short macro boundary. -/
theorem bounded_loop (input : RAMInput) (tape : ℕ→Bool) (B : ℕ) (s : Store)
    (src dst : Buffer) (width : ℕ) (runs : List (List SparseEntry))
    (hw : 0<width) (hp : PackedRuns width runs)
    (h : Bounded B s.val src dst width runs.flatten) :
    ∃cost t, BoundedExecutes B 30 input tape loopCode cost s t := by
  induction runs using List.twoStepInduction generalizing s src dst with
  | nil =>
    refine ⟨1,s,BoundedExecutes.done ?_ h.indices⟩
    rw [h.invariant.config.one,h.invariant.config.remaining]
    simp
  | singleton a =>
    by_cases he : a=[]
    · subst a
      refine ⟨1,s,BoundedExecutes.done ?_ h.indices⟩
      rw [h.invariant.config.one,h.invariant.config.remaining]
      simp
    · have ha : 0<a.length := List.length_pos_iff.mpr he
      have hh : Bounded B s.val src dst width (a++[]++[]) := by simpa using h
      have hl : a.length=min width (a++[]++[]).length := by simpa using (min_eq_right hp.1).symm
      have hr : ([] : List SparseEntry).length=min width ((a++[]++[]).length-a.length) := by simp
      obtain ⟨cost,t,_,run,hi,_,_,_,_⟩ := step input tape s src dst width a [] [] hh.invariant hl hr
      have bounded := bound_step_execution input tape B s src dst width a [] [] hh hl hr run
      have test : s.val.indices 1≤s.val.indices 17 := by
        rw [h.invariant.config.one,h.invariant.config.remaining]
        simp only [List.flatten_cons,List.flatten_nil,List.append_nil]
        omega
      exact ⟨1+cost+1,t,BoundedExecutes.more test bounded
        (.done (by rw [hi.config.one,hi.config.remaining]; simp) bounded.finish)⟩
  | cons_cons a b rest ih _ =>
    have hapos : 0<a.length := by rw [hp.2.1 (by simp)]; exact hw
    have hflat : (a::b::rest).flatten=a++b++rest.flatten := by simp [List.append_assoc]
    have hh : Bounded B s.val src dst width (a++b++rest.flatten) := by simpa only [hflat] using h
    have hl : a.length=min width (a++b++rest.flatten).length := by
      have ht := congrArg List.length (packed_pair_slices width a b rest hp).1
      simpa only [List.length_take,hflat] using ht.symm
    have hr : b.length=min width ((a++b++rest.flatten).length-a.length) := by
      have ht := congrArg List.length (packed_pair_slices width a b rest hp).2.1
      have hafull := hp.2.1 (by simp)
      simpa only [List.length_take,List.length_drop,hflat,hafull] using ht.symm
    obtain ⟨first,mid,_,run,hi,_,_,_,_⟩ := step input tape s src dst width a b rest.flatten hh.invariant hl hr
    have bounded := bound_step_execution input tape B s src dst width a b rest.flatten hh hl hr run
    have hb : Bounded B mid.val (src.shift (a.length+b.length))
        (dst.shift (a.length+b.length)) width rest.flatten := by
      refine ⟨hi,bounded.finish,hh.sourceEnd.subset ?_,hh.targetEnd.subset ?_,?_⟩
      · simp only [List.length_append]; omega
      · simp only [List.length_append]; omega
      · have hs := hh.size
        simp only [List.length_append] at hs
        omega
    obtain ⟨cost,t,tailRun⟩ := ih mid (src.shift (a.length+b.length)) (dst.shift (a.length+b.length))
      hp.2.2.2.2 hb
    have test : s.val.indices 1≤s.val.indices 17 := by
      rw [h.invariant.config.one,h.invariant.config.remaining,hflat]
      simp only [List.length_append]
      omega
    exact ⟨1+first+cost,t,BoundedExecutes.more test bounded tailRun⟩

theorem bound_execution (input : RAMInput) (tape : ℕ→Bool) (B : ℕ) (s : Store)
    (src dst : Buffer) (width : ℕ) (runs : List (List SparseEntry))
    (hw : 0<width) (hp : PackedRuns width runs)
    (h : Bounded B s.val src dst width runs.flatten)
    {cost : ℕ} {t : Store} (run : Executes input tape loopCode cost s t) :
    BoundedExecutes B 30 input tape loopCode cost s t := by
  obtain ⟨other,u,bounded⟩ := bounded_loop input tape B s src dst width runs hw hp h
  obtain ⟨rfl,rfl⟩ := run.deterministic bounded.executes
  exact bounded

end Maxwell.Cost.RealSparseOrder.Pass
