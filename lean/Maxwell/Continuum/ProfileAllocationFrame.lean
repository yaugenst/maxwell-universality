import Maxwell.Continuum.ProfileAllocationBounds
import Maxwell.Continuum.ProfileStartupPrecision

/-! Buffer allocation preserves the exact transform state produced by
runtime startup. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

theorem allocationBank_after_startup {N heap : ℕ} {s t : Store}
    (f : BinaryPrecision.Frame startupWorkspace s.val t.val)
    (h : NatAssign.Bank allocationIds (bufferInput N 0 heap) s.val)
    (hprecision : Word t.val 660 N) (hd : Word t.val 661 (profileDegree N)) :
    NatAssign.Bank allocationIds (bufferInput N (profileDegree N) heap) t.val := by
  intro i hi
  by_cases hD : i=661
  · subst i;simpa [bufferInput] using hd
  by_cases hN : i=660
  · subst i
    simpa [bufferInput] using hprecision
  have outside : i∉startupWorkspace := by
    simp only [allocationIds,bufferIds,bufferHeaderIds,Finset.mem_union,Finset.mem_insert,
      Finset.mem_singleton] at hi
    simp only [startupWorkspace,dimensionWorkspace,dimensionIds,parameterWorkspace,parameterIds,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    omega
  simpa only [bufferInput,ite_eq_right hN,ite_eq_right hD] using
    word_of_eq (f.tapes i outside) (h i hi)

def ProducerState.allocation_frame {grid D P U : ℕ} {s t : Store}
    (h : ProducerState grid D P U s) (z : NatAssign.Scratch t.val)
    (f : BinaryPrecision.Frame allocationWorkspace s.val t.val) : ProducerState grid D P U t := by
  have ready : Ready dftRegisters h.values t := by
    refine ⟨?_,z⟩
    have hd : Disjoint (ids dftRegisters) allocationWorkspace := by decide
    intro i hi
    exact word_of_eq (f.tapes i (fun hh=>Finset.disjoint_left.mp hd hi hh)) (h.ready.1 i hi)
  refine ⟨h.values,ready,h.width,h.saved,?_,h.savedWidth,h.innerWord,?_,h.innerLength,
    ?_,?_,?_,?_,word_of_eq (f.tapes 144 (by decide)) h.power,
    word_of_eq (f.tapes 664 (by decide)) h.gridWord⟩
  · exact ⟨word_of_eq (f.tapes 701 (by decide)) h.stored.1,
      word_of_eq (f.tapes 702 (by decide)) h.stored.2.1,
      word_of_eq (f.tapes 703 (by decide)) h.stored.2.2⟩
  · exact BankArray.word_of_eq (f.tapes 201 (by decide)) h.innerCounter
  · have hd : Disjoint ((PhaseMachine.Runtime.ids.erase 652).erase 653) allocationWorkspace := by decide
    intro i hi
    exact blank_of_eq (f.tapes i (fun hh=>Finset.disjoint_left.mp hd hi hh)) (h.phaseClean i hi)
  · have hd : Disjoint (GlueMachine.Runtime.ids.erase 640) allocationWorkspace := by decide
    intro i hi
    exact blank_of_eq (f.tapes i (fun hh=>Finset.disjoint_left.mp hd hi hh)) (h.glueClean i hi)
  · refine ⟨blank_of_eq (f.tapes 4 (by decide)) h.floorClean.1,?_⟩
    have hd : Disjoint (DyadicFloor.extraIds∪NaturalQuotient.workPorts) allocationWorkspace := by decide
    intro i hi
    exact blank_of_eq (f.tapes i (fun hh=>Finset.disjoint_left.mp hd hi hh)) (h.floorClean.2 i hi)
  · exact ⟨word_of_eq (f.tapes 663 (by decide)) h.parameters.precision,
      word_of_eq (f.tapes 667 (by decide)) h.parameters.one,
      word_of_eq (f.tapes 668 (by decide)) h.parameters.guard,
      word_of_eq (f.tapes 669 (by decide)) h.parameters.range,
      word_of_eq (f.tapes 652 (by decide)) h.parameters.phaseRange,
      word_of_eq (f.tapes 653 (by decide)) h.parameters.phasePrecision,
      word_of_eq (f.tapes 640 (by decide)) h.parameters.gluePrecision⟩

#print axioms allocationBank_after_startup
#print axioms ProducerState.allocation_frame
end Maxwell.Continuum.Profile.Runtime
