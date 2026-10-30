import Maxwell.Continuum.SourceRoutingSourcePlan

/-! Scratch and descriptor facts are recovered from the executed source
frontend, including its private incidence-pass tape renaming. -/

namespace Maxwell.Cost.RoutingPorts.Complete.SourcePlan
open Structured SourceGraph.Positive
open RationalAccumulator (Word Blank)
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000

theorem ready {S : Source.SparseSystem} {p : ℕ} {s : Store}
    (hs : SourceGraph.Incidence.Result S p s) : Ready s.val := by
  obtain ⟨clock,index,_,_,_,_,workspace⟩ := hs.configuration
  have keep (i : ℕ) (hi : i<10) :
      s.val.tapes i=(s.renameTapes GraphIncidence.relocation.symm).val.tapes i := by
    rw [GraphIncidence.renamed_tape,GraphIncidence.shiftBank_fixed i (by omega) (by omega)]
  obtain ⟨previous,hprevious,frame⟩ := hs.saved
  exact ⟨SourceCircuit.scratch_of_tapes workspace.1 keep,
    RationalAccumulator.blank_of_eq (keep 7 (by decide)) workspace.2.1,
    RationalAccumulator.blank_of_eq (frame.tapes 37 (by decide) (by decide)) hprevious.workspace.packed,
    ⟨0,hs.fresh 752 (by decide) (by decide) (by decide)⟩⟩

theorem descriptor {S : Source.SparseSystem} {p : ℕ} {s : Store}
    (hs : SourceGraph.Incidence.Result S p s) :
    ∃clock, Scatter.Descriptor (GraphIncidence.layout (width S p) (dimension S p) (count S p))
      clock s.val := by
  obtain ⟨previous,hprevious,frame⟩ := hs.saved
  obtain ⟨clock,hlen,hclock⟩ := hprevious.clock
  exact ⟨clock,⟨hs.numeric.widthWord,hs.numeric.endpointBase,
    BankArray.word_of_eq (frame.tapes 146 (by decide) (by decide)) hclock,
    hlen,hs.numeric.rankBase,hs.numeric.two,hs.numeric.clockTwo⟩⟩

theorem startup_fresh {S : Source.SparseSystem} {p : ℕ} {s : Store}
    (hs : SourceGraph.Incidence.Result S p s) : ∀i∈Startup.banks,Blank s.val i := by
  intro i hi
  have hrange : 700 ≤ i ∧ i < 752 := by
    simp only [Startup.banks,Size.banks,Finset.mem_union,Finset.mem_insert,
      Finset.mem_singleton,Finset.mem_Icc] at hi
    omega
  exact ⟨0,hs.fresh i (by omega) (Or.inr (by omega)) (Or.inr (by omega))⟩

#print axioms ready
#print axioms descriptor
#print axioms startup_fresh

end Maxwell.Cost.RoutingPorts.Complete.SourcePlan
