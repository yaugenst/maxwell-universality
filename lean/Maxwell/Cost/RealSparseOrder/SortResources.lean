import Maxwell.Cost.RealSparseOrder.BoundedSort

namespace Maxwell.Cost.RealSparseOrder.Sort
open RealSimulation.Control RealSimulation.IndexWidth

/-- The sort only copies and compares initialized constants; it introduces
no input-dependent literal words. -/
theorem literal_bound (B : ℕ) : LiteralBound B loopCode.compile := by
  have checked : loopCode.compile.code.all (fun op => match op with
      | .indexLiteral _ value => decide (value≤0)
      | _ => true)=true := by decide
  intro dst value h
  have hv := List.all_eq_true.mp checked (.indexLiteral dst value) h
  have hz : value≤0 := by simpa using hv
  omega

/-- The same actual execution has the near-linear-logarithmic instruction
bound and a uniform logarithmic index-word budget at every transition. -/
theorem resources (input : RAMInput) (tape : ℕ→Bool) (B : ℕ) (s : Store)
    (src dst : Buffer) (entries : List SparseEntry)
    (h : Bounded B s.val src dst 1 (singletonRuns entries))
    (hi : InputBound B input) :
    ∃cost t, cost≤108*entries.length*entries.length.size+16*entries.length.size+1 ∧
      Executes input tape loopCode cost s t ∧
      Records (bufferAfter entries.length.size src dst) t.val (bottomUpSort entries) ∧
      (bottomUpSort entries).Pairwise KeyLE ∧(bottomUpSort entries).Perm entries ∧
      RealSimulation.VisitedSteps (loopCode.compile.next input tape)
        (RealSimulation.IndexWordWidth (30+B.size)) cost s.val (t.place loopCode.size) ∧
      Frame src dst entries.length s.val t.val := by
  obtain ⟨cost,t,hcost,run,records,sorted,perm,frame⟩ :=
    sorted_records input tape s src dst entries h.invariant
  have bounded := bound_execution input tape B s src dst entries h run
  exact ⟨cost,t,hcost,run,records,sorted,perm,bounded.word_width (literal_bound B) hi,frame⟩

end Maxwell.Cost.RealSparseOrder.Sort
