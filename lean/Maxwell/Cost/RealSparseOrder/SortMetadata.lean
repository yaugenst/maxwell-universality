import Maxwell.Cost.RealSparseOrder.BoundedSort

namespace Maxwell.Cost.RealSparseOrder.Sort
open RealSimulation.Control

def Metadata (s t : RAMState) : Prop := ∀j,32≤j → j<100 → t.indices j=s.indices j

theorem step_metadata (input : RAMInput) (tape : ℕ→Bool) (s : Store)
    (src dst : Buffer) (width : ℕ) (runs : List (List SparseEntry))
    (hw : 0<width) (hp : PackedRuns width runs) (h : Invariant s.val src dst width runs)
    {cost : ℕ} {t : Store} (actual : Executes input tape stepCode cost s t) : Metadata s.val t.val := by
  let start := Store.ofState (OuterControl.prepared s.val)
  have hs : Pass.Invariant start.val src dst width runs.flatten :=
    (Pass.invariant_ofState _ _ _ _ _).mpr h.prepared
  obtain ⟨n,mid,_,run,_,_,_,control,_⟩ := Pass.executes input tape start src dst width runs hw hp hs
  have full : Executes input tape stepCode (6+(n+8)) s
      (Store.ofState (OuterControl.advanced mid.val)) :=
    .seq (OuterControl.prepare_executes input tape s) (.seq run (OuterControl.advance_executes input tape mid))
  obtain ⟨_,rfl⟩ := actual.deterministic full
  intro j hj hk
  exact (OuterControl.advance_indices_frame mid.val j (Or.inr (Or.inr hj))).trans
    ((control j (by omega) hk).trans
      (OuterControl.prepare_indices_frame s.val j (Or.inr (Or.inr (by omega)))))

private theorem metadata_passes (input : RAMInput) (tape : ℕ→Bool) (k j : ℕ)
    (s : Store) (src dst : Buffer) (runs : List (List SparseEntry))
    (h : Invariant s.val src dst (2^j) runs) (hp : PackedRuns (2^j) runs)
    (hk : j+k=runs.flatten.length.size) :
    ∃cost t,Executes input tape loopCode cost s t ∧Metadata s.val t.val := by
  induction k generalizing j s src dst runs with
  | zero =>
    refine ⟨1,s,Executes.done ?_,?_⟩
    · rw [h.config.width,h.config.count]
      have he : j=runs.flatten.length.size := by omega
      rw [he]
      exact Nat.not_le.mpr (Nat.lt_size_self _)
    · intro _ _ _; rfl
  | succ k ih =>
    have hj : j<runs.flatten.length.size := by omega
    have test : s.val.indices 18≤s.val.indices 26 := by
      rw [h.config.width,h.config.count]
      exact Nat.lt_size.mp hj
    obtain ⟨first,mid,_,run,hi,_,_⟩ := step input tape s src dst (2^j) runs (by positivity) hp h
    have hm := step_metadata input tape s src dst (2^j) runs (by positivity) hp h run
    have hi' : Invariant mid.val dst src (2^(j+1)) (mergePass runs) := by
      simpa only [pow_succ,Nat.mul_comm] using hi
    have hp' : PackedRuns (2^(j+1)) (mergePass runs) := by
      simpa only [pow_succ,Nat.mul_comm] using mergePass_packed (2^j) runs hp
    have hk' : (j+1)+k=(mergePass runs).flatten.length.size := by rw [mergePass_mass]; omega
    obtain ⟨cost,t,tailRun,hmetadata⟩ := ih (j+1) mid dst src (mergePass runs) hi' hp' hk'
    exact ⟨1+first+cost,t,.more test run tailRun,fun i hi hlo=>(hmetadata i hi hlo).trans (hm i hi hlo)⟩

/-- Descriptor and physical-calibration metadata above the fixed sort
scratch bank survives the actual whole loop. -/
theorem metadata (input : RAMInput) (tape : ℕ→Bool) (s : Store)
    (src dst : Buffer) (entries : List SparseEntry)
    (h : Invariant s.val src dst 1 (singletonRuns entries))
    {cost : ℕ} {t : Store} (actual : Executes input tape loopCode cost s t) : Metadata s.val t.val := by
  obtain ⟨other,u,run,hmeta⟩ := metadata_passes input tape entries.length.size 0 s src dst (singletonRuns entries)
    (by simpa using h) (by simpa using singletonRuns_packed entries) (by simp)
  obtain ⟨_,rfl⟩ := actual.deterministic run
  exact hmeta

end Maxwell.Cost.RealSparseOrder.Sort
