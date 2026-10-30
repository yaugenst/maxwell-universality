import Maxwell.Continuum.CutoffAllocatedBuffer

/-! Loaded polynomial buffers retain their computed intervals. These facts
justify the second allocation and the actual alternating-buffer recurrence. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

theorem cacheBuffer_end (D W heap : ℕ) (memory : ℕ→Bool) :
    ∀base∈([ (cacheBuffer D W heap memory).basePositive,
      (cacheBuffer D W heap memory).baseNegative,
      (cacheBuffer D W heap memory).baseDenominator]:List (List Bool)),
      addressValue base+4*(D+1)*addressValue (cacheBuffer D W heap memory).width≤cacheNextBase D W heap := by
  intro base hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hb
  rcases hb with rfl|rfl|rfl <;>
    simp only [cacheBuffer,Profile.Runtime.memoryTable,addressValue_bits,cacheNextBase,Nat.mul_assoc] <;> omega

theorem loadedBuffer_end {n D W : ℕ} (a : Table n) (heap : ℕ) (memory : ℕ→Bool)
    (stride offset : ℕ) :
    ∀base∈([ (loadedMonomialTable a (cacheBuffer D W heap memory) stride offset).basePositive,
      (loadedMonomialTable a (cacheBuffer D W heap memory) stride offset).baseNegative,
      (loadedMonomialTable a (cacheBuffer D W heap memory) stride offset).baseDenominator]:List (List Bool)),
      addressValue base+4*(D+1)*addressValue
        (loadedMonomialTable a (cacheBuffer D W heap memory) stride offset).width≤cacheNextBase D W heap := by
  have h := loadedMonomialTable_metadata a (cacheBuffer D W heap memory) stride offset
  simpa only [h.1,h.2.1,h.2.2.1,h.2.2.2.1] using cacheBuffer_end D W heap memory

theorem loadedBuffers_disjoint {n D W : ℕ} (a : Table n) (heap : ℕ) (memory memory' : ℕ→Bool)
    (firstStride firstOffset secondStride secondOffset : ℕ) :
    (loadedMonomialTable a (cacheBuffer D W heap memory) firstStride firstOffset).SeparatedFrom
      (loadedMonomialTable (loadedMonomialTable a (cacheBuffer D W heap memory) firstStride firstOffset)
        (cacheBuffer D W (cacheNextBase D W heap) memory') secondStride secondOffset) := by
  have h := loadedMonomialTable_metadata a (cacheBuffer D W heap memory) firstStride firstOffset
  have g := loadedMonomialTable_metadata (loadedMonomialTable a (cacheBuffer D W heap memory) firstStride firstOffset)
    (cacheBuffer D W (cacheNextBase D W heap) memory') secondStride secondOffset
  unfold Table.SeparatedFrom
  rw [g.1,g.2.1,g.2.2.1,g.2.2.2.1,h.1,h.2.1,h.2.2.1,h.2.2.2.1]
  exact cache_buffers_separated D W heap memory memory'

theorem loadedBuffers_valid {n D W : ℕ} (a : Table n) (heap : ℕ) (hh : heap.bits.length≤W)
    (memory memory' : ℕ→Bool) (coeff : ℕ→Parts)
    (v : ℕ→Parts) (hv : WidthBank (Finset.range 8) W v) (hg : Good (Finset.range 8) v)
    (htwo : v 5=Parts.literal 2)
    (hfirst : MonomialStored (loadedMonomialTable a (cacheBuffer D W heap memory) 1 0)
      (monomialState D coeff 0))
    (hcoeff1 : MonomialCoefficientsStored (loadedMonomialTable a (cacheBuffer D W heap memory) 1 0) coeff)
    (hsecond : MonomialStored
      (loadedMonomialTable (loadedMonomialTable a (cacheBuffer D W heap memory) 1 0)
        (cacheBuffer D W (cacheNextBase D W heap) memory') 4 7) (monomialState D coeff 0))
    (hcoeff2 : MonomialCoefficientsStored
      (loadedMonomialTable (loadedMonomialTable a (cacheBuffer D W heap memory) 1 0)
        (cacheBuffer D W (cacheNextBase D W heap) memory') 4 7) coeff) :
    (⟨loadedMonomialTable a (cacheBuffer D W heap memory) 1 0,
      loadedMonomialTable (loadedMonomialTable a (cacheBuffer D W heap memory) 1 0)
        (cacheBuffer D W (cacheNextBase D W heap) memory') 4 7,v⟩ : MonomialCache D).Valid W coeff 0 := by
  have h := loadedMonomialTable_metadata a (cacheBuffer D W heap memory) 1 0
  have g := loadedMonomialTable_metadata (loadedMonomialTable a (cacheBuffer D W heap memory) 1 0)
    (cacheBuffer D W (cacheNextBase D W heap) memory') 4 7
  have m1 := (cache_table_metadata D W heap hh memory).1
  have m2 := (cache_table_metadata D W heap hh memory').2
  have s1 := Profile.Runtime.memoryTable_separated (4*(D+1)) (monomialWorkingWidth D W) heap
    (cache_working_pos D W) memory
  have s2 := Profile.Runtime.memoryTable_separated (4*(D+1)) (monomialWorkingWidth D W)
    (cacheNextBase D W heap) (cache_working_pos D W) memory'
  refine ⟨Profile.Runtime.tableMetadata_width h m1,Profile.Runtime.tableMetadata_width g m2,
    ?_,?_,Profile.Runtime.tableMetadata_separated h s1,Profile.Runtime.tableMetadata_separated g s2,
    loadedBuffers_disjoint a heap memory memory' 1 0 4 7,hfirst,hsecond.1,hcoeff1,hcoeff2,
    hv.mono (by unfold monomialStorageWidth;omega),hg,htwo⟩
  · change monomialWorkingWidth D W≤addressValue (loadedMonomialTable a (cacheBuffer D W heap memory) 1 0).width
    rw [h.1]
    simp only [cacheBuffer,Profile.Runtime.memoryTable,addressValue_bits]
    exact le_rfl
  · change monomialWorkingWidth D W≤addressValue (loadedMonomialTable
      (loadedMonomialTable a (cacheBuffer D W heap memory) 1 0)
      (cacheBuffer D W (cacheNextBase D W heap) memory') 4 7).width
    rw [g.1]
    simp only [cacheBuffer,Profile.Runtime.memoryTable,addressValue_bits]
    exact le_rfl

#print axioms loadedBuffers_disjoint
#print axioms loadedBuffers_valid
end Maxwell.Continuum.Calibration.RawCutoff
