import Maxwell.Continuum.CutoffCacheBoundary
import Maxwell.Continuum.CutoffCacheAdvance

/-! The two-buffer cache is built by a fixed program from the actual profile
input table. The second allocation reads coefficients from the initialized
first buffer, so no auxiliary memory-preservation assumption is needed. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Blank)
set_option maxHeartbeats 4500000
set_option maxRecDepth 32768

private theorem loaded_five {n : ℕ} (a : Table n) (D stride offset : ℕ) (v : ℕ→Parts) :
    loadedMonomialValues a D stride offset v 5=v 5 :=
  (laneCopyRowsValues_other a D stride offset 1 _ D 5 (by decide)).trans
    (Function.update_of_ne (by decide) _ _)

def cachePairCode : Code := .seq (allocateInitialCode false)
  (.seq headerSwapCode (.seq cacheAdvanceCode (allocateInitialCode true)))
def cachePairCost (D W oldlen : ℕ) : ℕ := allocateInitialCost D W oldlen+
  (256*(monomialWorkingWidth D W+1)+(1024*(monomialWorkingWidth D W+1)+
    allocateInitialCost D W D.bits.length))

theorem cachePair_executes {p D W : ℕ} (a : Table D) (old : Table p)
    (heap : ℕ) (hD : 2≤D) (hW : 2≤W) (hh : heap.bits.length≤W)
    (haMeta : a.MetadataWidth W) (hoMeta : old.MetadataWidth W)
    (hend : ∀base∈([a.basePositive,a.baseNegative,a.baseDenominator]:List (List Bool)),
      addressValue base+D*addressValue a.width≤heap)
    (hc : ∀r<D,(a.getD r).Valid) (hw : ∀r<D,(a.getD r).Width W)
    (v : ℕ→Parts) (hv : WidthBank (Finset.range 8) W v) (hg : Good (Finset.range 8) v)
    (htwo : v 5=Parts.literal 2)
    (input : List Bool) (tape : ℕ→Bool) (oldWord : List Bool) (s : Store)
    (hs : RationalDataflow.Ready (Finset.range 8) v s) (ha : a.Ready s) (ho : old.OutputReady s)
    (hcount : BankArray.Word s.val 201 oldWord) (hdegree : RationalAccumulator.Word s.val 720 D)
    (hnat : NatAssign.Bank Profile.Runtime.CacheAllocation.inputs (cacheAllocatorValues D W heap 3) s.val)
    (hnext : RationalAccumulator.Word s.val 729 (cacheNextBase D W heap))
    (hblank : ∀i∈RowIndex.ids,Blank s.val i) (hswap : Blank s.val 216) :
    ∃(cost : ℕ) (t : Store) (word : List Bool) (cache : MonomialCache D),Executes input tape cachePairCode cost s t ∧
      cost≤cachePairCost D W oldWord.length ∧ cache.Valid W a.getD 0 ∧
      RationalDataflow.Ready (Finset.range 8) cache.bank t ∧ cache.current.Ready t ∧ cache.spare.OutputReady t ∧
      (∀i∈RowIndex.ids,Blank t.val i) ∧ Blank t.val 216 ∧
      BankArray.Word t.val 201 word ∧ word.length=D.bits.length ∧
      RationalAccumulator.Word t.val 720 D ∧
      RationalAccumulator.Word t.val 725 (4*(D+1)) ∧
      RationalAccumulator.Word t.val 726 (monomialWorkingWidth D W) ∧
      RationalAccumulator.Word t.val 727 (cacheNextBase D W heap) ∧
      RationalAccumulator.Word t.val 728 (4*(D+1)*monomialWorkingWidth D W) ∧
      (∀i∈([206,207,208,209,709,721,722,723,724,729]:List ℕ),t.val.tapes i=s.val.tapes i) ∧ cache.EndsBefore (cacheEndBase D W heap) := by
  let B := monomialWorkingWidth D W
  have hWB : W≤B := by dsimp [B,monomialWorkingWidth,monomialStorageWidth];omega
  have hB : 3≤B := by dsimp [B,monomialWorkingWidth];omega
  have header := cache_header_bound D W heap hh
  obtain ⟨c0,s0,w0,e0,hc0,r0,a0,b0,z0,swap0,count0,len0,degree0,size0,width0,heap0,temp0,
    vw0,vg0,stored0,coeff0,keep0⟩ := allocateInitial_executes a old false heap 3 hD hW
    (haMeta.mono hWB) (hoMeta.mono hWB) header.1
    (by change (3:ℕ).bits.length≤B;rw [show (3:ℕ).bits.length=2 from rfl];omega)
    hend (by simp [cacheSourceStride,cacheSourceOffset]) a.getD
    (by intro r hr;simp [cacheSourceStride,cacheSourceOffset]) hc hw v hv hg input tape oldWord s
    hs ha ho hcount hdegree hnat hblank hswap
  let first := loadedMonomialTable a (cacheBuffer D W heap s.val.memory) 1 0
  let v0 := loadedMonomialValues a D 1 0 v
  change RationalDataflow.Ready (Finset.range 8) v0 s0 at r0
  change first.OutputReady s0 at b0
  change WidthBank (Finset.range 8) W v0 at vw0
  change Good (Finset.range 8) v0 at vg0
  change MonomialStored first (monomialState D a.getD 0) at stored0
  change MonomialCoefficientsStored first a.getD at coeff0
  have fm := loadedMonomialTable_metadata a (cacheBuffer D W heap s.val.memory) 1 0
  have fmeta : first.MetadataWidth B := Profile.Runtime.tableMetadata_width fm
    (cache_table_metadata D W heap hh s.val.memory).1
  obtain ⟨c1,s1,e1,hc1,r1,b1,a1,swap1,f1⟩ := headerSwap_executes a first B
    (haMeta.mono hWB) fmeta (Finset.range 8) v0 input tape s0 r0 a0 b0 swap0
  have next0 := RationalAccumulator.word_of_eq (keep0 729 (by decide)) hnext
  have heap1 := RationalAccumulator.word_of_eq (f1.tapes 727 (by decide)) heap0
  have next1 := RationalAccumulator.word_of_eq (f1.tapes 729 (by decide)) next0
  obtain ⟨c2,s2,e2,hc2,heap2,next2,z2,f2⟩ := cacheAdvance_executes heap (cacheNextBase D W heap)
    input tape s1 heap1 next1 r1.2
  have r2 := cacheAdvance_rational_frame r1 f2 z2
  have b2 := cacheAdvance_table_frame b1 f2 z2
  have a2 := cacheAdvance_output_frame a1 f2 b2.scratch b2.seven
  have middle_keep (i : ℕ) (hi : i≠727) (hzero : 4 ≤ i)
      (hheader : i∉insert 216 headerSlots) : s2.val.tapes i=s0.val.tapes i :=
    (f2.tapes i (by simp only [NatAssign.changed,Finset.mem_insert,Finset.mem_singleton];omega)).trans
      (f1.tapes i hheader)
  have degree2 := RationalAccumulator.word_of_eq (middle_keep 720 (by decide) (by decide) (by decide)) degree0
  have size2 := RationalAccumulator.word_of_eq (middle_keep 725 (by decide) (by decide) (by decide)) size0
  have width2 := RationalAccumulator.word_of_eq (middle_keep 726 (by decide) (by decide) (by decide)) width0
  have temp2 := RationalAccumulator.word_of_eq (middle_keep 728 (by decide) (by decide) (by decide)) temp0
  have count2 := BankArray.word_of_eq (middle_keep 201 (by decide) (by decide) (by decide)) count0
  have swap2 := RationalAccumulator.blank_of_eq (f2.tapes 216 (by decide)) swap1
  have index2 : ∀i∈RowIndex.ids,Blank s2.val i := by
    intro i hi
    apply RationalAccumulator.blank_of_eq (middle_keep i (by
      simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton] at hi;omega) (by
      simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton] at hi;omega) _) (z0 i hi)
    simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl <;> decide
  have nat2 : NatAssign.Bank Profile.Runtime.CacheAllocation.inputs
      (cacheAllocatorValues D W (cacheNextBase D W heap) (4*(D+1)*B)) s2.val := by
    intro i hi
    simp only [Profile.Runtime.CacheAllocation.inputs,Finset.mem_Icc] at hi
    rcases hi with ⟨hlo,hhi⟩
    interval_cases i <;> simp only [cacheAllocatorValues,ite_true]
    · exact size2
    · exact width2
    · exact heap2
    · exact temp2
  have tempWidth : (4*(D+1)*B).bits.length≤B := by
    have h := RationalAccumulator.bits_mul_le (4*(D+1)) B
    dsimp only [B] at h ⊢
    omega
  have secondCoeff (r : ℕ) (hr : r<D) : first.getD (cacheSourceStride true*r+cacheSourceOffset true)=a.getD r :=
    coeff0 ⟨r,hr⟩
  obtain ⟨c3,t,word,e3,hc3,r3,first3,spare3,z3,swap3,count3,len3,degree3,size3,width3,heap3,temp3,
    vw3,vg3,stored3,coeff3,keep3⟩ := allocateInitial_executes first a true (cacheNextBase D W heap)
    (4*(D+1)*B) hD hW fmeta (haMeta.mono hWB) header.2 tempWidth
    (loadedBuffer_end a heap s.val.memory 1 0) (by intro r hr;change 4*r+7<4*(D+1);omega)
    a.getD secondCoeff hc hw v0 vw0 vg0 input tape w0 s2 r2 b2 a2 count2 degree2 nat2 index2 swap2
  let spare := loadedMonomialTable first (cacheBuffer D W (cacheNextBase D W heap) s2.val.memory) 4 7
  let v3 := loadedMonomialValues first D 4 7 v0
  change RationalDataflow.Ready (Finset.range 8) v3 t at r3
  change spare.OutputReady t at spare3
  change WidthBank (Finset.range 8) W v3 at vw3
  change Good (Finset.range 8) v3 at vg3
  change MonomialStored spare (monomialState D a.getD 0) at stored3
  change MonomialCoefficientsStored spare a.getD at coeff3
  have two3 : v3 5=Parts.literal 2 :=
    (loaded_five first D 4 7 v0).trans ((loaded_five a D 1 0 v).trans htwo)
  let cache : MonomialCache D := ⟨first,spare,v3⟩
  have valid : cache.Valid W a.getD 0 := loadedBuffers_valid a heap hh s.val.memory s2.val.memory
    a.getD v3 vw3 vg3 two3 stored0 coeff0 stored3 coeff3
  refine ⟨c0+(c1+(c2+c3)),t,word,cache,e0.seq (e1.seq (e2.seq e3)),?_,valid,r3,first3,spare3,
    z3,swap3,count3,len3,degree3,size3,width3,heap3,temp3,?_,loadedBuffers_end a heap s.val.memory s2.val.memory v3⟩
  · have advance : c2≤1024*(B+1) := by
      have hn : (cacheNextBase D W heap).bits.length≤B := by omega
      have hhB : heap.bits.length≤B := hh.trans hWB
      omega
    rw [len0] at hc3
    exact Nat.add_le_add hc0 (Nat.add_le_add hc1 (Nat.add_le_add advance hc3))
  · intro i hi
    apply (keep3 i hi).trans
    apply (middle_keep i (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi;omega) (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi;omega) _).trans (keep0 i hi)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

#print axioms cachePair_executes
end Maxwell.Continuum.Calibration.RawCutoff
