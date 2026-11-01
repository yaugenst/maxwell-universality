import Maxwell.Continuum.RationalDataflowArrayNormalizeMachine
import Maxwell.Continuum.RationalDataflowArrayNormalizeAllocated
import Maxwell.Continuum.CalibrationFourierTableData
import Maxwell.Continuum.CalibrationGlobalNormalization
import Maxwell.Continuum.CalibrationFiniteSeedNormPositive

/-! Exact Fourier meaning of the executed array-normalization program.
The finite seed supplies its own proof that the computed norm is positive. -/
namespace Maxwell.Continuum.Calibration.GlobalPower
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow RationalDataflow.PartArray
open scoped BigOperators
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

theorem tableData_normalized (R P : ℕ) (a b : Table (2*aliasArraySize R))
    (values : ∀i,(b.get i).value=
      (sqrtRationalCenter (∑j,(a.get j).value^2) P)⁻¹*(a.get i).value) :
    tableData R b=FourierData.normalizeData P (tableData R a) := by
  unfold tableData
  rw [←normalized_data]
  congr 1
  exact congrArg (unpack R) (funext values)

theorem tableData_normCenter (R P : ℕ) (a : Table (2*aliasArraySize R)) :
    FourierData.normCenter P (tableData R a)=
      sqrtRationalCenter (∑i,(a.get i).value^2) P := normCenter_unpack R P _

/-- Actual normalization of a generated finite seed. All storage and width
conditions describe the machine input; norm positivity follows from the
physical lower bound on the cell length. -/
theorem seed_executes {L : ℕ} (hL : MasterConstants.Ls≤(L:ℝ)) (r N R : ℕ)
    (a b : Table (2*aliasArraySize R)) (n : ℕ→ℕ) (v : ℕ→Parts) (W : ℕ) (hW : 1≤W)
    (precision : n 700=FiniteAlgorithm.precision L r N)
    (data : tableData R a=FiniteAlgorithm.rawSeed L r N)
    (naturalWidth : ∀i∈RationalRoot.Stored.ids 24,(n i).bits.length≤W)
    (rawWidth : WidthBank Normalize.slots W v) (good : Good Normalize.slots v)
    (entryWidth : ∀i,(a.get i).Width W) (entryValid : ∀i,(a.get i).Valid)
    (countWidth : (2*aliasArraySize R).bits.length≤W) (metadata : a.MetadataWidth W)
    (outputMetadata : b.MetadataWidth (2*Normalize.width (2*aliasArraySize R) (n 700) W+1))
    (capacity : 2*Normalize.width (2*aliasArraySize R) (n 700) W+1≤addressValue b.width)
    (separated : b.Separated) (disjoint : a.SeparatedFrom b)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ)
    (length : xs.length≤W) (s : Store) (count : addressValue xs=2*aliasArraySize R)
    (counter : s.val.tapes 201=BitTape.shifted xs origin)
    (savedCount : RationalAccumulator.Word s.val 787 (2*aliasArraySize R))
    (bank : NatAssign.Bank (RationalRoot.Stored.ids 24) n s.val)
    (raw : Ready Normalize.slots v s) (array : a.Ready s) (output : b.OutputReady s) :
    ∃cost t,∃result : Table (2*aliasArraySize R),
      Executes input tape Normalize.code cost s t ∧
      cost≤Normalize.costBound (2*aliasArraySize R) (n 700) W xs.length ∧
      result.OutputReady t ∧
      result.MetadataWidth (2*Normalize.width (2*aliasArraySize R) (n 700) W+1) ∧
      (∀i,(result.get i).Valid) ∧
      (∀i,(result.get i).Width (2*Normalize.width (2*aliasArraySize R) (n 700) W+1)) ∧
      tableData R result=FiniteAlgorithm.seed L r N ∧
      (result.width=b.width ∧ result.basePositive=b.basePositive ∧ result.baseNegative=b.baseNegative ∧
        result.baseDenominator=b.baseDenominator ∧ result.clock=b.clock) ∧
      (∀limit,limit≤addressValue b.basePositive→limit≤addressValue b.baseNegative→
        limit≤addressValue b.baseDenominator→∀j,j<limit→t.val.memory j=s.val.memory j) := by
  have positive : 0<sqrtRationalCenter (∑i,(a.get i).value^2) (n 700) := by
    rw [←tableData_normCenter,precision,data]
    exact FiniteAlgorithm.rawSeed_normCenter_pos hL r N
  obtain ⟨cost,t,result,execution,bound,ready,description,valid,width,values,headers,memory,_⟩ :=
    Normalize.executes a b n v W hW naturalWidth rawWidth good entryWidth entryValid
      countWidth metadata outputMetadata capacity separated disjoint positive input tape xs origin
      length s count counter savedCount bank raw array output
  refine ⟨cost,t,result,execution,bound,ready,description,valid,width,?_,headers,memory⟩
  rw [tableData_normalized R (n 700) a result values,precision,data]
  rfl

#print axioms tableData_normalized
#print axioms seed_executes

/-- The finite-seed normalizer computes its own storage capacity and heap
layout before evaluating the norm and every output coefficient. -/
theorem seed_allocated_executes {L : ℕ} (hL : MasterConstants.Ls≤(L:ℝ)) (r N R : ℕ)
    (a : Table (2*aliasArraySize R)) (n : ℕ→ℕ) (v : ℕ→Parts)
    (B H : ℕ) (hB : 10≤B)
    (width : ∀k∈Normalize.Allocation.allIds,(n k).bits.length≤B)
    (count : n 788=2*aliasArraySize R)
    (precision : n 700=FiniteAlgorithm.precision L r N)
    (data : tableData R a=FiniteAlgorithm.rawSeed L r N)
    (good : Good Normalize.slots v) (entryValid : ∀i,(a.get i).Valid)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank Normalize.Allocation.allIds n s.val)
    (array : a.Ready s) (raw : Ready Normalize.slots v s)
    (h37 : RationalAccumulator.Blank s.val 37) (h216 : RationalAccumulator.Blank s.val 216)
    (headers : WordCleanup.Bounded PowerMachine.BufferNorm.Allocation.clearHeaders H s.val) :
    ∃cost t,∃result : Table (2*aliasArraySize R),
      Executes input tape Normalize.allocatedCode cost s t ∧
      cost≤Normalize.allocatedCost n B H ∧ result.OutputReady t ∧
      result.MetadataWidth (Normalize.Allocation.capacity n) ∧
      (∀i,(result.get i).Valid) ∧ (∀i,(result.get i).Width (Normalize.Allocation.capacity n)) ∧
      tableData R result=FiniteAlgorithm.seed L r N ∧
      (result.width=(Normalize.Allocation.capacity n).bits ∧
        result.basePositive=(Normalize.Allocation.heap n).bits ∧
        result.baseNegative=(Normalize.Allocation.heap n+n 788*Normalize.Allocation.capacity n).bits ∧
        result.baseDenominator=(Normalize.Allocation.heap n+2*n 788*Normalize.Allocation.capacity n).bits ∧
        result.clock=List.replicate (Normalize.Allocation.capacity n) false) ∧
      RationalAccumulator.Word t.val 574 (Normalize.Allocation.heapEnd n) ∧
      (∀j,j<Normalize.Allocation.heap n→t.val.memory j=s.val.memory j) := by
  have positive : 0<sqrtRationalCenter (∑i,(a.get i).value^2) (n 700) := by
    rw [←tableData_normCenter,precision,data]
    exact FiniteAlgorithm.rawSeed_normCenter_pos hL r N
  obtain ⟨cost,t,result,execution,bound,ready,description,valid,fit,values,metadataEq,heapWord,memory⟩ :=
    Normalize.allocated_executes n a v B H hB width count good entryValid positive input tape s
      bank array raw h37 h216 headers
  refine ⟨cost,t,result,execution,bound,ready,description,valid,fit,?_,metadataEq,heapWord,memory⟩
  rw [tableData_normalized R (n 700) a result values,precision,data]
  rfl

#print axioms seed_allocated_executes
end Maxwell.Continuum.Calibration.GlobalPower
