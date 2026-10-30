import Maxwell.Continuum.ProfileCacheInput
import Maxwell.Continuum.RationalDataflowProgramFootprint

/-! The generated profile leaves the later cache metadata untouched and
returns the index scratch empty as part of its proved division-bank contract. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
open Calibration.RawCutoff
set_option maxHeartbeats 4500000
set_option maxRecDepth 32768
set_option exponentiation.threshold 2048

def cacheFreshPorts : Finset ℕ := {206,207,208,209}∪cacheDimensionIds

theorem producer_protects_cache : producerCode.protectsSet cacheFreshPorts=true := by decide

theorem EncodedTableResult.indexBlanks {N W : ℕ} {a : Table (profileDegree N)} {s : Store}
    (r : EncodedTableResult N W a s) : ∀i∈RowIndex.ids,RationalAccumulator.Blank s.val i := by
  intro i hi
  have hm : i∈NaturalQuotient.workPorts := by
    simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl <;> decide
  have h := r.ready.1 i (Finset.mem_union_right _ hm)
  rw [SharedConversion.work_values_zero r.values i hm] at h
  exact (RationalAccumulator.zero_word_iff_blank _ _).mp h

#print axioms producer_protects_cache
#print axioms EncodedTableResult.indexBlanks
end Maxwell.Continuum.Profile.Runtime
