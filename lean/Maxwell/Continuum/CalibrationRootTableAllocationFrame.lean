import Maxwell.Continuum.CalibrationRootTableAllocation

/-! Allocation preserves the literal arithmetic and elementary-evaluation
banks, while exposing its computed natural metadata. -/
namespace Maxwell.Continuum.RationalDataflow.RootTable
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

theorem allocatedChanged_small (i : ℕ) (hi : i∈allocatedChanged) :
    i<4 ∨ (200 ≤ i ∧ i≤573) := by
  rw [allocatedChanged_eq] at hi
  simp only [Finset.mem_insert,Finset.mem_singleton] at hi
  omega

theorem Context.allocation_frame {S : Finset ℕ} {N : ℕ} {n m : ℕ→ℕ} {v : ℕ→Parts}
    {s t : Store} (h : Context S N n v s)
    (f : BinaryPrecision.Frame allocatedChanged s.val t.val)
    (hb : NatAssign.Bank RootFrequency.ids m t.val) (hz : ∀i,i<5 → Blank t.val i) :
    Context S N m v t := by
  have rational : Ready S v t := by
    refine ⟨?_,fun i hi => hz i (by omega)⟩
    intro i hi
    have hge := ids_ge_ten S i hi
    apply word_of_eq (f.tapes i _) (h.rational.1 i hi)
    intro hm
    have ha := allocatedChanged_small i hm
    exact outside_workspace S i (Or.inr (by omega)) (Finset.mem_union_right _ hi)
  have glue : Glue.Clean t.val := by
    intro i hi
    by_cases hs : i<5
    · exact hz i hs
    have disjoint : Disjoint ((GlueMachine.Runtime.ids.erase 640)\Finset.range 5)
        allocatedChanged := by rw [allocatedChanged_eq];decide
    have hout := Finset.disjoint_left.mp disjoint
      (Finset.mem_sdiff.mpr ⟨hi,by simpa only [Finset.mem_range] using hs⟩)
    exact blank_of_eq (f.tapes i hout) (h.glue i hi)
  have phase : Phase.Runtime.Clean t.val := by
    intro i hi
    by_cases hs : i<5
    · exact hz i hs
    have disjoint : Disjoint (((PhaseMachine.Runtime.ids.erase 652).erase 653)\Finset.range 5)
        allocatedChanged := by rw [allocatedChanged_eq];decide
    have hout := Finset.disjoint_left.mp disjoint
      (Finset.mem_sdiff.mpr ⟨hi,by simpa only [Finset.mem_range] using hs⟩)
    exact blank_of_eq (f.tapes i hout) (h.phase i hi)
  exact ⟨rational,hb,hz,glue,phase,
    word_of_eq (f.tapes 640 (by rw [allocatedChanged_eq];decide)) h.glue_precision,
    word_of_eq (f.tapes 652 (by rw [allocatedChanged_eq];decide)) h.phase_range,
    word_of_eq (f.tapes 653 (by rw [allocatedChanged_eq];decide)) h.phase_precision⟩

theorem storageValues_work_zero (v : ℕ→ℕ)
    (hv : ∀i∈NaturalQuotient.workPorts,v i=0) :
    ∀i∈NaturalQuotient.workPorts,storageValues v i=0 := by
  intro i hi
  have hh := hi
  simp only [NaturalQuotient.workPorts,Finset.mem_insert,Finset.mem_singleton] at hh
  rw [storageValues_keep v i (by omega)]
  exact hv i hi

theorem storageValues_grid (v : ℕ→ℕ) : storageValues v 331=v 331 :=
  storageValues_keep v 331 (by decide)

#print axioms Context.allocation_frame
end Maxwell.Continuum.RationalDataflow.RootTable
