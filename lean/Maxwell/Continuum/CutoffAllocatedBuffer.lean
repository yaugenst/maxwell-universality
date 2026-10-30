import Maxwell.Continuum.CutoffCacheAllocationFrame

/-! Allocation and initialization execute as one fixed program. Old output
memory is arbitrary; the result stores the actual runtime coefficient lane. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Blank)
set_option maxHeartbeats 4500000
set_option maxRecDepth 32768

def cacheBuffer (D W heap : ℕ) (memory : ℕ→Bool) : Table (4*(D+1)) :=
  Profile.Runtime.memoryTable (4*(D+1)) (monomialWorkingWidth D W) heap (cache_working_pos D W) memory

def cacheAllocatorValues (D W heap temp : ℕ) (i : ℕ) : ℕ :=
  if i=725 then 4*(D+1) else if i=726 then monomialWorkingWidth D W
  else if i=727 then heap else if i=728 then temp else 0

def allocateInitialCode (second : Bool) : Code :=
  .seq Profile.Runtime.CacheAllocation.code (monomialInitializeCode second)

def allocateInitialCost (D W oldlen : ℕ) : ℕ :=
  2^60*(3*monomialWorkingWidth D W+3)^2+
    monomialInitializeCost D (monomialWorkingWidth D W) oldlen

theorem cacheAllocator_output_ports (D W heap temp : ℕ) :
    Profile.Runtime.CacheAllocation.outputValues (cacheAllocatorValues D W heap temp) 726=monomialWorkingWidth D W ∧
    Profile.Runtime.CacheAllocation.outputValues (cacheAllocatorValues D W heap temp) 727=heap ∧
    Profile.Runtime.CacheAllocation.outputValues (cacheAllocatorValues D W heap temp) 728=4*(D+1)*monomialWorkingWidth D W := by
  simp [Profile.Runtime.CacheAllocation.outputValues,Profile.Runtime.CacheAllocation.plan,
    Profile.Runtime.CacheAllocation.clearedValues,Profile.Runtime.CacheAllocation.headerIds,
    cacheAllocatorValues,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
    NatAssign.Instruction.value]
  ring

theorem allocateInitial_executes {n p D W : ℕ} (a : Table n) (old : Table p)
    (second : Bool) (heap temp : ℕ) (hD : 2≤D) (hW : 2≤W)
    (haMeta : a.MetadataWidth (monomialWorkingWidth D W))
    (hoMeta : old.MetadataWidth (monomialWorkingWidth D W))
    (hheader : heap.bits.length+(4*(D+1)).bits.length+(monomialWorkingWidth D W).bits.length+4≤
      monomialWorkingWidth D W)
    (htemp : temp.bits.length≤monomialWorkingWidth D W)
    (hend : ∀base∈([a.basePositive,a.baseNegative,a.baseDenominator]:List (List Bool)),
      addressValue base+n*addressValue a.width≤heap)
    (hsource : ∀r<D,cacheSourceStride second*r+cacheSourceOffset second<n)
    (coeff : ℕ→Parts) (hcoeff : ∀r<D,a.getD (cacheSourceStride second*r+cacheSourceOffset second)=coeff r)
    (hc : ∀r<D,(coeff r).Valid) (hw : ∀r<D,(coeff r).Width W)
    (v : ℕ→Parts) (hv : WidthBank (Finset.range 8) W v) (hg : Good (Finset.range 8) v)
    (input : List Bool) (tape : ℕ→Bool) (oldWord : List Bool) (s : Store)
    (hs : RationalDataflow.Ready (Finset.range 8) v s) (ha : a.Ready s) (ho : old.OutputReady s)
    (hcount : BankArray.Word s.val 201 oldWord) (hdegree : RationalAccumulator.Word s.val 720 D)
    (hnat : NatAssign.Bank Profile.Runtime.CacheAllocation.inputs (cacheAllocatorValues D W heap temp) s.val)
    (hblank : ∀i∈RowIndex.ids,Blank s.val i) (hswap : Blank s.val 216) :
    ∃cost t finalWord,Executes input tape (allocateInitialCode second) cost s t ∧
      cost≤allocateInitialCost D W oldWord.length ∧
      RationalDataflow.Ready (Finset.range 8)
        (loadedMonomialValues a D (cacheSourceStride second) (cacheSourceOffset second) v) t ∧
      a.Ready t ∧
      (loadedMonomialTable a (cacheBuffer D W heap s.val.memory)
        (cacheSourceStride second) (cacheSourceOffset second)).OutputReady t ∧
      (∀i∈RowIndex.ids,Blank t.val i) ∧ Blank t.val 216 ∧
      BankArray.Word t.val 201 finalWord ∧ finalWord.length=D.bits.length ∧
      RationalAccumulator.Word t.val 720 D ∧ RationalAccumulator.Word t.val 725 (4*(D+1)) ∧
      RationalAccumulator.Word t.val 726 (monomialWorkingWidth D W) ∧
      RationalAccumulator.Word t.val 727 heap ∧
      RationalAccumulator.Word t.val 728 (4*(D+1)*monomialWorkingWidth D W) ∧
      WidthBank (Finset.range 8) W
        (loadedMonomialValues a D (cacheSourceStride second) (cacheSourceOffset second) v) ∧
      Good (Finset.range 8)
        (loadedMonomialValues a D (cacheSourceStride second) (cacheSourceOffset second) v) ∧
      MonomialStored (loadedMonomialTable a (cacheBuffer D W heap s.val.memory)
        (cacheSourceStride second) (cacheSourceOffset second)) (monomialState D coeff 0) ∧
      MonomialCoefficientsStored (loadedMonomialTable a (cacheBuffer D W heap s.val.memory)
        (cacheSourceStride second) (cacheSourceOffset second)) coeff ∧
      (∀i∈([206,207,208,209,709,721,722,723,724,729]:List ℕ),t.val.tapes i=s.val.tapes i) := by
  let B := monomialWorkingWidth D W
  let nv := cacheAllocatorValues D W heap temp
  have hVB : W≤B := by dsimp [B,monomialWorkingWidth,monomialStorageWidth];omega
  have inputWidth (i : ℕ) (hi : i∈Profile.Runtime.CacheAllocation.inputs) : (nv i).bits.length≤B := by
    simp only [Profile.Runtime.CacheAllocation.inputs,Finset.mem_Icc] at hi
    rcases hi with ⟨hlo,hhi⟩
    interval_cases i <;> simp [nv,cacheAllocatorValues] <;> omega
  obtain ⟨c0,s0,e0,hc0,a0,b0,bank0,_,swap0,f0⟩ := Profile.Runtime.CacheAllocation.executes a old nv B B
    (cache_working_pos D W) inputWidth hoMeta input tape s hnat ha ho hswap
  change (cacheBuffer D W heap s.val.memory).OutputReady s0 at b0
  have z0 : NatAssign.Scratch s0.val := by
    intro i hi
    interval_cases i
    · exact a0.scratch.1
    · exact a0.scratch.2.1
    · exact a0.scratch.2.2.1
    · exact a0.scratch.2.2.2.1
  have r0 := cacheAllocation_rational_frame hs f0 z0
  have count0 := BankArray.word_of_eq (f0.tapes 201 (by decide)) hcount
  have degree0 := RationalAccumulator.word_of_eq (f0.tapes 720 (by decide)) hdegree
  have size0 : RationalAccumulator.Word s0.val 725 (4*(D+1)) := by
    have h := bank0 725 (by simp [Profile.Runtime.CacheAllocation.ids,Profile.Runtime.CacheAllocation.inputs])
    rw [show Profile.Runtime.CacheAllocation.outputValues nv 725=nv 725 by
      exact Profile.Runtime.CacheAllocation.plan_keep _ _ (by decide)] at h
    exact h
  have indexBlanks : ∀i∈RowIndex.ids,Blank s0.val i := by
    intro i hi
    apply RationalAccumulator.blank_of_eq (f0.tapes i _) (hblank i hi)
    simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl <;> decide
  have bm := Profile.Runtime.memoryTable_metadata (4*(D+1)) B heap B (cache_working_pos D W)
    s.val.memory le_rfl hheader
  have bs := Profile.Runtime.memoryTable_separated (4*(D+1)) B heap (cache_working_pos D W) s.val.memory
  have bd := cacheTable_disjoint_after a D W heap s.val.memory hend
  have hDlen : D.bits.length≤B := by
    have h := cache_nat_bits_le D
    dsimp [B,monomialWorkingWidth,monomialStorageWidth]
    omega
  obtain ⟨c1,t,word,e1,hc1,r1,a1,b1,z1,swap1,count1,len1,degree1,size1,width1,good1,stored1,coeff1⟩ :=
    monomialInitialize_executes a (cacheBuffer D W heap s.val.memory) second B W hD (by omega) hVB
      haMeta bm (by simp only [cacheBuffer,Profile.Runtime.memoryTable,addressValue_bits];exact le_rfl)
      bs bd hsource hDlen (by omega) coeff hcoeff hc hw v hv hg input tape oldWord s0 r0 a0 b0 count0
      degree0 size0 indexBlanks swap0
  have ports := cacheAllocator_output_ports D W heap temp
  have width0 : RationalAccumulator.Word s0.val 726 (monomialWorkingWidth D W) := by
    simpa only [nv,ports.1] using bank0 726 (by simp [Profile.Runtime.CacheAllocation.ids,Profile.Runtime.CacheAllocation.inputs])
  have heap0 : RationalAccumulator.Word s0.val 727 heap := by
    simpa only [nv,ports.2.1] using bank0 727 (by simp [Profile.Runtime.CacheAllocation.ids,Profile.Runtime.CacheAllocation.inputs])
  have temp0 : RationalAccumulator.Word s0.val 728 (4*(D+1)*monomialWorkingWidth D W) := by
    simpa only [nv,ports.2.2] using bank0 728 (by simp [Profile.Runtime.CacheAllocation.ids,Profile.Runtime.CacheAllocation.inputs])
  refine ⟨c0+c1,t,word,e0.seq e1,?_,r1,a1,b1,z1,swap1,count1,len1,degree1,size1,
    RationalAccumulator.word_of_eq (initialize_keeps_auxiliary e1 726 (by decide)) width0,
    RationalAccumulator.word_of_eq (initialize_keeps_auxiliary e1 727 (by decide)) heap0,
    RationalAccumulator.word_of_eq (initialize_keeps_auxiliary e1 728 (by decide)) temp0,
    width1,good1,stored1,coeff1,?_⟩
  · have hc0' : c0≤2^60*(3*B+3)^2 := by
      change c0≤2^60*(B+B+B+3)^2 at hc0
      rwa [show B+B+B+3=3*B+3 by omega] at hc0
    exact Nat.add_le_add hc0' hc1
  · intro i hi
    have hlist : i∈([206,207,208,209,709,721,722,723,724,726,727,728,729]:List ℕ) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      tauto
    exact (initialize_keeps_auxiliary e1 i hlist).trans (f0.tapes i (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide))

#print axioms allocateInitial_executes
end Maxwell.Continuum.Calibration.RawCutoff
