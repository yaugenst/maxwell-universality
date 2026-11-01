import Maxwell.Continuum.CalibrationBasisCoefficient
import Maxwell.Continuum.CalibrationInverseAllocatedTapeBound
import Maxwell.Continuum.RationalDataflowBankInclusions

/-! A basis column starts with physical scalar words and arbitrary memory.
The program creates its forcing, allocates coefficient storage, computes the
inverse descriptors, and executes the cached inverse. -/
namespace Maxwell.Continuum.Calibration.BasisForcing.Inverse
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open FreeFiber RationalDataflow PartArray ArrayDecodeMachine NeumannMachine
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384
attribute [local irreducible] bank sourceTable CoefficientAllocation.budget
  CoefficientAllocation.slotWidth CoefficientAllocation.slotOffset
  inputCost CoefficientAllocation.costBound allocationWidth metadataWidth workWidth prepareWidth

def code (column : Fin 24) : Code := .seq (CoefficientInput.code column) AllocatedInverse.code

def costBound (n extra cold nf : ℕ→ℕ) (B H I X length D : ℕ) : ℕ :=
  let cn:=CoefficientInput.joined n nf extra
  let Q:=CoefficientAllocation.budget cn
  let slot:=CoefficientAllocation.slotWidth Q
  let heap:=CoefficientAllocation.heap cn
  let q:=InverseDescriptor.selected (n 311) slot heap Q cold
  let d:=InverseDescriptor.values q
  inputCost (n 311) B H I length+
        CoefficientAllocation.costBound cn (CoefficientInput.joinWidth B) (metadataWidth B)+6*allocationWidth B+5+
        InverseDescriptor.startCost (InverseDescriptor.inputs (n 311) slot heap Q cold)
          (InverseDescriptor.inputBound (n 311) slot heap Q X (CoefficientAllocation.metadataWidth (CoefficientInput.joinWidth B)))+
        AllocatedInverse.inverseCost (n 311) Q (InverseDescriptor.rawWidth q) (InverseDescriptor.bankWidth q)
          slot D d

private theorem neighbors : RawFree.neighborRegisters⊆bank := by
  unfold RawFree.neighborRegisters bank
  exact Finset.range_mono (by decide : 41≤232)

private theorem parameters : matrixParameters⊆RawFree.neighborRegisters := by decide
private theorem parameters_retained : matrixParameters⊆retained := by decide

private theorem quasi_kept (v w : ℕ→Parts) (keep:∀k∈retained,w k=v k) :
    RawFree.quasiParts w=RawFree.quasiParts v := by
  funext j
  fin_cases j <;> exact keep _ (by decide)

theorem executes (column : Fin 24) (n extra cold : ℕ→ℕ) (v : ℕ→Parts)
    (agree : ∀k∈ids bank,n k=dataValues v k) (good : Good bank v)
    (B H I X : ℕ) (hB : 103≤B) (hR : 3≤n 311)
    (hw : ∀k∈allocationIds,(n k).bits.length≤B)
    (ew : ∀k∈CoefficientInput.extraIds,(extra k).bits.length≤B)
    (cw : ∀k∈InverseDescriptor.coldIds,(cold k).bits.length≤X)
    (hv : ∀k∈retained,(v k).Width B)
    (ht : (3:ℝ)≤(v 0).value) (hE : (7:ℝ)≤(v 1).value ∧ ((v 1).value:ℝ)≤8)
    (hr : ∀k,|((RawFree.quasiParts v k).value:ℝ)|≤1/16)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (s : Store)
    (hs : NatAssign.Bank allocationIds n s.val)
    (he : NatAssign.Bank CoefficientInput.extraIds extra s.val)
    (hcold : NatAssign.Bank InverseDescriptor.coldIds cold s.val)
    (hz : BankArray.Scratch s.val) (h4 : RationalAccumulator.Blank s.val 4)
    (h7 : RationalAccumulator.Blank s.val 7) (h37 : RationalAccumulator.Blank s.val 37)
    (h206 : RationalAccumulator.Blank s.val 206) (h216 : RationalAccumulator.Blank s.val 216)
    (oldOutput : WordCleanup.Bounded PowerMachine.BufferNorm.Allocation.clearHeaders H s.val)
    (oldInput : WordCleanup.Bounded Promote.headers I s.val) (hword : BankArray.Word s.val 201 xs) :
    ∃(cost : ℕ) (t : Store) (nf : ℕ→ℕ)
        (coeff : CoefficientIndex (aliasArraySize (n 311))→Parts) (out : Snapshot (aliasArraySize (n 311))),
      let cn:=CoefficientInput.joined n nf extra
      let Q:=CoefficientAllocation.budget cn
      let slot:=CoefficientAllocation.slotWidth Q
      let heap:=CoefficientAllocation.heap cn
      let q:=InverseDescriptor.selected (n 311) slot heap Q cold
      let d:=InverseDescriptor.values q
      Executes input tape (code column) cost s t ∧
      cost ≤ costBound n extra cold nf B H I X xs.length (SharedTable.denominator coeff) ∧
      (∀i,(coeff i).Valid ∧ (coeff i).Width (InverseDescriptor.rawWidth q) ∧
        (coeff i).value=cachedCoefficientTable (v 0).value (v 1).value
          (fun j=>(RawFree.quasiParts v j).value) (n 311) (rationalRightCoupling (rationalBasisField column)) i) ∧
      out.Ready (aliasArraySize (n 311)).bits (AllocatedInverse.outputWidth (n 311) (SharedTable.denominator coeff) d) t.val ∧
      out.data.Sized (AllocatedInverse.outputWidth (n 311) (SharedTable.denominator coeff) d) ∧
      RationalAccumulator.Word t.val 126 (SharedTable.denominator coeff) ∧
      RationalAccumulator.Word t.val 304 (n 311-3) ∧
      RationalAccumulator.Blank t.val 140 ∧
      (∃numbers : ℕ→ℕ,NatAssign.Bank Descriptors.retainedIds numbers t.val ∧
        ∀k∈Descriptors.retainedIds,(numbers k).bits.length ≤ Descriptors.retainedWidth (d 301)) ∧
      (∃numbers : ℕ→ℕ,NatAssign.Bank (Finset.Icc 311 332) numbers t.val ∧
         (∀k∈Finset.Icc 311 332,(numbers k).bits.length ≤ d 301) ∧ numbers 311=n 311) ∧
      WordCleanup.Bounded conversionRetiredWords (d 301) t.val ∧
      RationalAccumulator.Blank t.val 105 ∧
      (∃raw : ℕ→Parts,Cells bank raw t.val ∧
        WidthBank bank (max (d 301) (prepareWidth (allocationWidth B))) raw) ∧
      NatAssign.Bank (Finset.Icc 530 534) d t.val ∧
      (∀k∈Finset.Icc 530 534,(d k).bits.length≤InverseDescriptor.bankWidth q) ∧
      NatAssign.Bank CoefficientAllocation.workIds (CoefficientAllocation.allocatedWork cn) t.val ∧
      (∀k∈CoefficientAllocation.workIds,(CoefficientAllocation.allocatedWork cn k).bits.length ≤
        CoefficientAllocation.allocatedWorkWidth (CoefficientInput.joinWidth B)) ∧
      NatAssign.Bank AllocatedInverse.inactiveIds d t.val ∧
      (∀k∈AllocatedInverse.inactiveIds,(d k).bits.length ≤ InverseDescriptor.bankWidth q) ∧
      RationalAccumulator.Word t.val 376 (n 376) ∧
      ∀i:Fin (aliasArraySize (n 311)),((Horner.channels out.words 10 11).value i:ℚ)/(SharedTable.denominator coeff:ℚ)^(n 311-2)=
        (cachedInverseApply (v 0).value (v 1).value (fun j=>(RawFree.quasiParts v j).value)
          (n 311) (rationalRightCoupling (rationalBasisField column)) (n 311-2)).get i := by
  obtain ⟨c0,u,a,b,vf,nf,e0,cost0,source,target,_,width,aMeta,bMeta,separated,disjoint,layout,
    valid,agrees,radius,keep,sourceCells,sourceWidth,emission,widths,aValid,value,zero,z201,z206,z216,budget,count,slotWord,baseWord,allocatedWork,allocatedWidth,_,_,_,frame,heapWord⟩:=
    CoefficientInput.executes column n extra v agree good B H I hB (by omega) hw ew hv input tape xs s
      hs he hz h4 h7 h37 h206 h216 oldOutput oldInput hword
  let cn:=CoefficientInput.joined n nf extra
  let Q:=CoefficientAllocation.budget cn
  let slot:=CoefficientAllocation.slotWidth Q
  let heap:=CoefficientAllocation.heap cn
  have neighborsIds:=ids_mono neighbors
  have naturalAgreement (k : ℕ) (hk:k∈ids RawFree.neighborRegisters) : cn k=dataValues vf k := by
    exact (CoefficientInput.natural (n 311) (n 376) nf extra _ radius k
      (naturalIds_parts (neighborsIds hk))).trans (agrees k (neighborsIds hk))
  have rawWidths : WidthBank RawFree.neighborRegisters Q vf :=
    widthBank_of_naturals _ cn vf Q naturalAgreement (fun k hk=>widths k (Finset.mem_union_left _ (Finset.mem_union_left _ hk)))
  have physical (k : ℕ) (hk:k∈matrixParameters) : (vf k).Width Q ∧ (vf k).Valid :=
    ⟨rawWidths k (parameters hk),valid k (neighbors (parameters hk))⟩
  have zeroKeep:vf 0=v 0:=keep 0 (by decide)
  have oneKeep:vf 1=v 1:=keep 1 (by decide)
  have quasiKeep:=quasi_kept v vf keep
  have coldBank : NatAssign.Bank InverseDescriptor.coldIds cold u.val := by
    intro k hk
    apply RationalAccumulator.word_of_eq (frame k (InverseDescriptor.cold_continuation hk) _) (hcold k hk)
    simp only [InverseDescriptor.coldIds,Finset.mem_union,Finset.mem_Icc] at hk
    omega
  have large:101≤Q:=(CoefficientAllocation.budget_ge cn).trans' (by decide)
  obtain ⟨c1,t,coeff,out,e1,cost1,coeffValid,ready,sized,denominator,remaining,blank,retained,controls,retired,blank105,inverseCells,working,workingWidth,persistent,inactive,inactiveWidth,result⟩:=
    AllocatedInverse.executes (n 311) heap Q slot X (CoefficientAllocation.metadataWidth (CoefficientInput.joinWidth B))
      hR large a b vf cn cold naturalAgreement widths physical rfl cw aValid aMeta bMeta layout width
      (by exact le_of_eq (CoefficientAllocation.slotWidth_eq Q).symm) separated disjoint
      (by simpa only [zeroKeep] using ht) (by simpa only [oneKeep] using hE)
      (by simpa only [quasiKeep] using hr) input tape u source target emission coldBank zero z201 z206 z216
      count slotWord baseWord budget
  obtain ⟨inverseParts,inverseCells,inverseWidth⟩:=inverseCells
  let after : ℕ→Parts := fun i=>if i∈RawFree.neighborRegisters then inverseParts i else vf i
  have afterCells : Cells bank after t.val := by
    intro i hi
    by_cases small:i∈RawFree.neighborRegisters
    · simpa only [after,ite_eq_left small] using inverseCells i small
    · simp only [after,ite_eq_right small]
      have low : 41 ≤ i := by simpa only [RawFree.neighborRegisters,Finset.mem_range,not_lt] using small
      have keep (k : ℕ) (hk : 1123 ≤ k) : t.val.tapes k=u.val.tapes k :=
        e1.tapeBound k (AllocatedInverse.tapeBound.trans hk)
      exact ⟨RationalAccumulator.word_of_eq (keep _ (by unfold positivePort;omega)) (sourceCells i hi).1,
        RationalAccumulator.word_of_eq (keep _ (by unfold positivePort;omega)) (sourceCells i hi).2.1,
        RationalAccumulator.word_of_eq (keep _ (by unfold positivePort;omega)) (sourceCells i hi).2.2⟩
  have afterWidth : WidthBank bank
      (max (InverseDescriptor.values (InverseDescriptor.selected (n 311) slot heap Q cold) 301)
        (prepareWidth (allocationWidth B))) after := by
    intro i hi
    by_cases small:i∈RawFree.neighborRegisters
    · simpa only [after,ite_eq_left small] using (inverseWidth i small).mono (le_max_left _ _)
    · simpa only [after,ite_eq_right small] using (sourceWidth i hi).mono (le_max_right _ _)
  refine ⟨c0+c1,t,nf,coeff,out,e0.seq e1,?_,?_,ready,sized,denominator,remaining,blank,retained,controls,retired,blank105,⟨after,afterCells,afterWidth⟩,working,workingWidth,?_,allocatedWidth,inactive,inactiveWidth,
    RationalAccumulator.word_of_eq (persistent 376 (by decide)) heapWord,?_⟩
  · dsimp only [costBound]
    dsimp only [cn,Q,slot,heap] at cost1
    exact (Nat.add_le_add cost0 cost1).trans (by omega)
  · intro i
    simpa only [zeroKeep,oneKeep,quasiKeep,value] using coeffValid i
  · intro k hk
    exact RationalAccumulator.word_of_eq (persistent k
      ((by decide : CoefficientAllocation.workIds⊆AllocatedInverse.persistentPorts) hk)) (allocatedWork k hk)
  · intro i
    simpa only [zeroKeep,oneKeep,quasiKeep,value] using result i

#print axioms executes
end Maxwell.Continuum.Calibration.BasisForcing.Inverse
