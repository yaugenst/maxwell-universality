import Maxwell.Continuum.RationalDataflowStoredParts

/-! Raw rational cells can remain stored while unrelated arithmetic scratch
is occupied. Reconstruct the full arithmetic Ready state only at its boundary. -/
namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured

def Cells (S : Finset ℕ) (v : ℕ→Parts) (s : BitRAMState) : Prop :=
  ∀i∈S,StoredParts.Stored (positivePort i) (v i) s

theorem Cells.of_ready {S : Finset ℕ} {v : ℕ→Parts} {s : Store} (h:Ready S v s) : Cells S v s.val := by
  intro i hi
  refine ⟨?_,?_,?_⟩
  · simpa only [dataValues_positive] using h.1 (positivePort i) (cell_mem hi (by simp [cellPorts]))
  · rw [show positivePort i+1=negativePort i from rfl]
    simpa only [dataValues_negative] using h.1 (negativePort i) (cell_mem hi (by simp [cellPorts]))
  · rw [show positivePort i+2=denominatorPort i from rfl]
    simpa only [dataValues_denominator] using h.1 (denominatorPort i) (cell_mem hi (by simp [cellPorts]))

theorem Cells.bank {S : Finset ℕ} {v : ℕ→Parts} {s : BitRAMState} (h : Cells S v s) :
    NatAssign.Bank (ports S) (dataValues v) s := by
  intro i hi
  obtain ⟨j,hj,cell⟩:=Finset.mem_biUnion.mp hi
  simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at cell
  rcases cell with rfl|rfl|rfl
  · simpa only [dataValues_positive] using (h j hj).1
  · rw [dataValues_negative]
    exact (h j hj).2.1
  · rw [dataValues_denominator]
    exact (h j hj).2.2

theorem Cells.transfer_tapes {S : Finset ℕ} {v : ℕ→Parts} {s t : BitRAMState} (h : Cells S v s)
    (keep : ∀i∈ports S,t.tapes i=s.tapes i) : Cells S v t := by
  intro j hj
  have owned (i : ℕ) (hi : i∈cellPorts j) : i∈ports S := Finset.mem_biUnion.mpr ⟨j,hj,hi⟩
  exact ⟨RationalAccumulator.word_of_eq (keep _ (owned _ (by simp [cellPorts]))) (h j hj).1,
    RationalAccumulator.word_of_eq (keep _ (owned _ (by simp [cellPorts,negativePort,positivePort]))) (h j hj).2.1,
    RationalAccumulator.word_of_eq (keep _ (owned _ (by simp [cellPorts,denominatorPort,positivePort]))) (h j hj).2.2⟩

theorem Cells.transfer {S : Finset ℕ} {v : ℕ→Parts} {s t : BitRAMState} (h:Cells S v s)
    (keep:∀k,1000≤k→t.tapes k=s.tapes k) : Cells S v t := by
  intro i hi
  exact ⟨RationalAccumulator.word_of_eq (keep _ (positivePort_ge i)) (h i hi).1,
    RationalAccumulator.word_of_eq (keep _ (negativePort_ge i)) (h i hi).2.1,
    RationalAccumulator.word_of_eq (keep _ (denominatorPort_ge i)) (h i hi).2.2⟩

theorem Cells.write {S : Finset ℕ} {v : ℕ→Parts} {target : ℕ} {x : Parts} {s t : BitRAMState}
    (h:Cells S v s) (stored:StoredParts.Stored (positivePort target) x t)
    (frame:BinaryPrecision.Frame (cellPorts target) s t) : Cells S (Function.update v target x) t := by
  intro i hi
  by_cases eq:i=target
  · subst i;simpa only [Function.update_self] using stored
  · simp only [Function.update_of_ne eq]
    apply (h i hi).frame frame
    apply Finset.disjoint_left.mpr
    intro k hk ht
    simp only [StoredParts.ports,cellPorts,positivePort,negativePort,denominatorPort,
      Finset.mem_insert,Finset.mem_singleton] at hk ht
    omega

theorem Cells.ready {S : Finset ℕ} {v : ℕ→Parts} {s : Store} (cells:Cells S v s.val)
    (work:∀k∈workPorts,RationalAccumulator.Blank s.val k) (scratch:NatAssign.Scratch s.val) : Ready S v s := by
  refine ⟨?_,scratch⟩
  intro k hk
  rcases Finset.mem_union.mp hk with hp|hw
  · obtain ⟨i,hi,hk⟩:=Finset.mem_biUnion.mp hp
    simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at hk
    rcases hk with rfl|rfl|rfl
    · simpa only [dataValues_positive] using (cells i hi).1
    · rw [dataValues_negative]
      exact (cells i hi).2.1
    · rw [dataValues_denominator]
      exact (cells i hi).2.2
  · have low:k<1000:=by
      simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton] at hw
      omega
    rw [dataValues_small v low,RationalAccumulator.zero_word_iff_blank]
    exact work k hw

#print axioms Cells.ready
end Maxwell.Continuum.RationalDataflow
