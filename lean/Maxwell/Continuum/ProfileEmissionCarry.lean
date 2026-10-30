import Maxwell.Continuum.ProfileProducedFrame
import Maxwell.Continuum.ProfileEndpointCorrection
import Maxwell.Continuum.RationalDataflowProgramFootprint

/-! The endpoint-correction pass retains the actual dyadic scale and header
words required to emit its computed table. Its division scratch is proved empty. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def emissionPorts : Finset ℕ := {663,140,142,143}

theorem finalizeCode_preserves_emission : finalizeCode.protectsSet emissionPorts=true := by decide

theorem floorClean_headerSwap {s t : Store} (h : DyadicFloor.Clean s.val)
    (f : BinaryPrecision.Frame (insert 216 PartArray.headerSlots) s.val t.val) : DyadicFloor.Clean t.val := by
  have hd : Disjoint (insert 4 (DyadicFloor.extraIds∪NaturalQuotient.workPorts))
      (insert 216 PartArray.headerSlots) := by decide
  refine ⟨blank_of_eq (f.tapes 4 (fun hh=>Finset.disjoint_left.mp hd (by simp) hh)) h.1,?_⟩
  intro i hi
  exact blank_of_eq (f.tapes i (fun hh=>Finset.disjoint_left.mp hd (Finset.mem_insert_of_mem hi) hh)) (h.2 i hi)

theorem finalize_floorClean {input : List Bool} {tape : ℕ→Bool} {cost : ℕ} {s t : Store}
    (ex : Executes input tape finalizeCode cost s t) (h : DyadicFloor.Clean s.val)
    {v : ℕ→Parts} (hr : SharedConversion.Ready dftRegisters v t) : DyadicFloor.Clean t.val := by
  refine ⟨hr.2 4 (by decide),?_⟩
  intro i hi
  rcases Finset.mem_union.mp hi with he|hq
  · have hm : i∈emissionPorts := by
      simp only [DyadicFloor.extraIds,Finset.mem_insert,Finset.mem_singleton] at he
      rcases he with rfl|rfl|rfl <;> decide
    exact blank_of_eq (ex.protectsSet emissionPorts finalizeCode_preserves_emission i hm)
      (h.2 i (Finset.mem_union_left _ he))
  · have hw := hr.1 i (Finset.mem_union_right _ hq)
    rw [SharedConversion.work_values_zero v i hq] at hw
    exact (zero_word_iff_blank _ _).mp hw

#print axioms finalize_floorClean
end Maxwell.Continuum.Profile.Runtime
