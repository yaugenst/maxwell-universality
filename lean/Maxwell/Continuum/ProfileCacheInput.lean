import Maxwell.Continuum.ProfileEncodedHandoff
import Maxwell.Continuum.ProfileProducerAllocated
import Maxwell.Continuum.CutoffCacheRuntimePrepare

/-! The computed profile output supplies the cache's literal width and
free-memory cursor. All numeric and address bounds follow from the producer. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
open Calibration.RawCutoff
open RationalAccumulator (Blank)
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384
set_option exponentiation.threshold 2048
attribute [local irreducible] runtimeBudget

def cacheSourceWidth (N : ℕ) : ℕ := bufferWidth N (profileDegree N)
def cacheSourceHeap (N heap : ℕ) : ℕ := bufferHeapEnd N (profileDegree N) heap

theorem cacheSourceWidth_ge (N : ℕ) : 9≤cacheSourceWidth N := by
  unfold cacheSourceWidth bufferWidth encodedTableWidth correctionWorkingWidth endpointWorkingWidth
  omega

theorem profileDegree_two (N : ℕ) : 2≤profileDegree N := by
  unfold profileDegree
  have h : 1≤N+256 := by omega
  have hmul : 128≤128*(N+256) := by omega
  have hp := Nat.pow_le_pow_left hmul 2
  norm_num at hp
  omega

theorem cacheSourceHeap_bits (N heap : ℕ) (hh : heap.bits.length≤producerSize N) :
    (cacheSourceHeap N heap).bits.length≤cacheSourceWidth N := by
  obtain ⟨hB,hN,hD⟩ := producerSize_input_bounds N
  have h := (bufferAddressValues_width N (profileDegree N) heap (producerSize N) hN hD hh hB
    709 (by decide)).trans ((allocationBound_runtime N).trans (runtimeBudget_le_bufferWidth N (profileDegree N)))
  simpa only [cacheSourceHeap,cacheSourceWidth,bufferAddressValues_eq,ite_eq_right (by decide : (709:ℕ)≠210),
    ite_eq_right (by decide : (709:ℕ)≠212),ite_eq_right (by decide : (709:ℕ)≠213),
    ite_eq_right (by decide : (709:ℕ)≠214),ite_eq_right (by decide : (709:ℕ)≠200),
    ite_eq_right (by decide : (709:ℕ)≠202),ite_eq_right (by decide : (709:ℕ)≠203),
    ite_eq_right (by decide : (709:ℕ)≠204),ite_true] using h

theorem EncodedTableResult.cache_source_end {N heap : ℕ} {memory : ℕ→Bool} {s : Store}
    (r : EncodedTableResult N (runtimeBudget N) (finalBuffer N heap memory) s) :
    ∀base∈([r.table.basePositive,r.table.baseNegative,r.table.baseDenominator]:List (List Bool)),
      addressValue base+profileDegree N*addressValue r.table.width≤cacheSourceHeap N heap := by
  rw [r.metadata.1,r.metadata.2.1,r.metadata.2.2.1,r.metadata.2.2.2.1]
  intro base hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl <;>
    simp only [finalBuffer,memoryTable,addressValue_bits,cacheSourceHeap,bufferHeapEnd,Nat.mul_assoc] <;> omega

theorem EncodedTableResult.cache_metadata {N heap : ℕ} {memory : ℕ→Bool} {s : Store}
    (r : EncodedTableResult N (runtimeBudget N) (finalBuffer N heap memory) s)
    (hh : heap.bits.length≤producerSize N) : r.table.MetadataWidth (cacheSourceWidth N) ∧
      r.input.MetadataWidth (cacheSourceWidth N) := by
  exact ⟨tableMetadata_width r.metadata (allocated_metadata N heap hh memory).2,
    r.inputMetadata.mono (runtimeBudget_le_bufferWidth N _)⟩

theorem EncodedTableResult.cache_width_word {N heap : ℕ} {memory : ℕ→Bool} {s t : Store}
    (r : EncodedTableResult N (runtimeBudget N) (finalBuffer N heap memory) s)
    (hr : r.table.Ready t) : RationalAccumulator.Word t.val 200 (cacheSourceWidth N) := by
  have h := hr.width
  rw [r.metadata.1] at h
  exact h


#print axioms cacheSourceHeap_bits
#print axioms EncodedTableResult.cache_source_end

end Maxwell.Continuum.Profile.Runtime
