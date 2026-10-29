import Maxwell.Cost.RealSparseOrder.SortStep

namespace Maxwell.Cost.RealSparseOrder.Sort
open RealSimulation.Control

private theorem loop_of_passes (input : RAMInput) (tape : ℕ→Bool) (k j : ℕ)
    (s : Store) (src dst : Buffer) (runs : List (List SparseEntry))
    (h : Invariant s.val src dst (2^j) runs) (hp : PackedRuns (2^j) runs)
    (hk : j+k=runs.flatten.length.size) :
    ∃cost t, cost≤54*mergeWork k runs+16*k+1 ∧Executes input tape loopCode cost s t ∧
      Invariant t.val (bufferAfter k src dst) (bufferAfter k dst src)
        (2^(j+k)) (mergePasses k runs) ∧
      Frame src dst runs.flatten.length s.val t.val ∧Merge.Channels s.val t.val := by
  induction k generalizing j s src dst runs with
  | zero =>
    refine ⟨1,s,by simp [mergeWork],?_,?_,Frame.refl _ _ _ _,⟨rfl,rfl,rfl⟩⟩
    · apply Executes.done
      rw [h.config.width,h.config.count]
      have he : j=runs.flatten.length.size := by omega
      rw [he]
      exact Nat.not_le.mpr (Nat.lt_size_self _)
    · simpa only [bufferAfter,mergePasses,Nat.add_zero] using h
  | succ k ih =>
    have hj : j<runs.flatten.length.size := by omega
    have test : s.val.indices 18≤s.val.indices 26 := by
      rw [h.config.width,h.config.count]
      exact Nat.lt_size.mp hj
    obtain ⟨first,mid,hfirst,run,hi,frame,channels⟩ :=
      step input tape s src dst (2^j) runs (by positivity) hp h
    have hi' : Invariant mid.val dst src (2^(j+1)) (mergePass runs) := by
      simpa only [pow_succ,Nat.mul_comm] using hi
    have hp' : PackedRuns (2^(j+1)) (mergePass runs) := by
      simpa only [pow_succ,Nat.mul_comm] using mergePass_packed (2^j) runs hp
    have hk' : (j+1)+k=(mergePass runs).flatten.length.size := by rw [mergePass_mass]; omega
    obtain ⟨cost,t,hcost,tailRun,hfinal,tailFrame,tailChannels⟩ :=
      ih (j+1) mid dst src (mergePass runs) hi' hp' hk'
    refine ⟨1+first+cost,t,?_,Executes.more test run tailRun,?_,?_,?_⟩
    · simp only [mergeWork]
      omega
    · simpa only [bufferAfter,mergePasses,Nat.add_assoc,Nat.add_comm 1 k] using hfinal
    · apply frame.trans
      simpa only [mergePass_mass] using tailFrame.symm
    · exact ⟨tailChannels.1.trans channels.1,tailChannels.2.1.trans channels.2.1,
        tailChannels.2.2.trans channels.2.2⟩

/-- The fixed outer loop performs exactly the required number of doubling
passes, chosen by comparisons against the stored input count. -/
theorem executes (input : RAMInput) (tape : ℕ→Bool) (s : Store)
    (src dst : Buffer) (entries : List SparseEntry)
    (h : Invariant s.val src dst 1 (singletonRuns entries)) :
    ∃cost t, cost≤108*entries.length*entries.length.size+16*entries.length.size+1 ∧
      Executes input tape loopCode cost s t ∧
      Invariant t.val (bufferAfter entries.length.size src dst)
        (bufferAfter entries.length.size dst src) (2^entries.length.size)
        (mergePasses entries.length.size (singletonRuns entries)) ∧
      Frame src dst entries.length s.val t.val ∧Merge.Channels s.val t.val := by
  obtain ⟨cost,t,hcost,run,hi,frame,channels⟩ := loop_of_passes input tape entries.length.size 0
    s src dst (singletonRuns entries) (by simpa using h)
    (by simpa using singletonRuns_packed entries) (by simp)
  refine ⟨cost,t,?_,run,?_,?_,channels⟩
  · have hw := bottomUpWork_le entries
    change mergeWork entries.length.size (singletonRuns entries)≤_ at hw
    nlinarith
  · simpa only [Nat.zero_add] using hi
  · simpa only [singletonRuns_flatten] using frame

theorem sorted_records (input : RAMInput) (tape : ℕ→Bool) (s : Store)
    (src dst : Buffer) (entries : List SparseEntry)
    (h : Invariant s.val src dst 1 (singletonRuns entries)) :
    ∃cost t, cost≤108*entries.length*entries.length.size+16*entries.length.size+1 ∧
      Executes input tape loopCode cost s t ∧
      Records (bufferAfter entries.length.size src dst) t.val (bottomUpSort entries) ∧
      (bottomUpSort entries).Pairwise KeyLE ∧(bottomUpSort entries).Perm entries ∧
      Frame src dst entries.length s.val t.val := by
  obtain ⟨cost,t,hc,hr,hi,hf,_⟩ := executes input tape s src dst entries h
  exact ⟨cost,t,hc,hr,hi.records,bottomUpSort_sorted entries,bottomUpSort_perm entries,hf⟩

end Maxwell.Cost.RealSparseOrder.Sort
