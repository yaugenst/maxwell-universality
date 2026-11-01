import Maxwell.Continuum.CalibrationNeumannCleanup
import Maxwell.Continuum.CalibrationBasisInverseTapeBound
import Maxwell.Continuum.CalibrationBasisInverseRetained
import Maxwell.Continuum.CalibrationSchurReadColumn

/-! One actual source generation and cached inverse is followed immediately
by its gathered Schur column. The source arithmetic bank stays represented
and bounded for charged reuse on the next column. -/
namespace Maxwell.Continuum.Calibration.BasisSchurColumn
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open FreeFiber RationalDataflow PartArray ArrayDecodeMachine NeumannMachine BasisForcing
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384
attribute [local irreducible] BasisForcing.bank SchurRow.nodeCount
  CoefficientAllocation.budget CoefficientAllocation.slotWidth CoefficientAllocation.slotOffset
  allocationWidth prepareWidth

def code (column : Fin 24) : Code := .seq (BasisForcing.Inverse.code column) (SchurReadColumn.code column)

theorem schur_ports (k : ℕ) (hk : k∈ports SchurRow.bank) : 1696 ≤ k := by
  obtain ⟨i,hi,hcell⟩:=Finset.mem_biUnion.mp hk
  have low : 232 ≤ i := by
    simp only [SchurRow.bank,Finset.mem_union,Finset.mem_Ico] at hi
    omega
  simp only [cellPorts,positivePort,negativePort,denominatorPort,Finset.mem_insert,Finset.mem_singleton] at hcell
  omega

theorem source_ports (k : ℕ) (hk : k∈ports BasisForcing.bank) : 1000 ≤ k ∧ k < 1696 := by
  obtain ⟨i,hi,hcell⟩:=Finset.mem_biUnion.mp hk
  have upper : i < 232 := by simpa only [BasisForcing.bank,Finset.mem_range] using hi
  simp only [cellPorts,positivePort,negativePort,denominatorPort,Finset.mem_insert,Finset.mem_singleton] at hcell
  omega

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
    (oldInput : WordCleanup.Bounded Promote.headers I s.val) (hword : BankArray.Word s.val 201 xs)
    (p : ℕ→Parts) (P : ℕ) (pwidth : WidthBank SchurRow.bank P p) (pgood : Good SchurRow.bank p)
    (pzero : p 232=v 0) (pone : p 233=v 1)
    (pquasi : ∀j : Fin 3,p (234+j.val)=RawFree.quasiParts v j)
    (pcells : Cells SchurRow.bank p s.val) :
    ∃(cost : ℕ) (t : Store) (nf : ℕ→ℕ) (D : ℕ) (out raw : ℕ→Parts),
      let cn:=CoefficientInput.joined n nf extra
      let Q:=CoefficientAllocation.budget cn
      let slot:=CoefficientAllocation.slotWidth Q
      let heap:=CoefficientAllocation.heap cn
      let q:=InverseDescriptor.selected (n 311) slot heap Q cold
      let d:=InverseDescriptor.values q
      let W:=max (AllocatedInverse.outputWidth (n 311) D d) P
      Executes input tape (code column) cost s t ∧
      cost ≤ BasisForcing.Inverse.costBound n extra cold nf B H I X xs.length D+
        SchurReadColumn.costBound D (n 311-3) W (InverseDescriptor.bankWidth q) ∧
      Ready SchurRow.bank out t ∧ Good SchurRow.bank out ∧
      WidthBank SchurRow.bank (SchurColumn.resultWidth SchurReadColumn.rows
        (SchurReadColumn.workingWidth D (n 311-3) W)) out ∧
      (∀row,(out (SchurRow.output row column)).value=
        cachedSchurMatrix (v 0).value (v 1).value
          (fun j=>(RawFree.quasiParts v j).value) (n 311-2) row column) ∧
      Cells BasisForcing.bank raw t.val ∧
      WidthBank BasisForcing.bank (max (d 301) (prepareWidth (allocationWidth B))) raw ∧
      (∃numbers,NatAssign.Bank Descriptors.retainedIds numbers t.val ∧
        ∀k∈Descriptors.retainedIds,(numbers k).bits.length ≤ Descriptors.retainedWidth (d 301)) ∧
      (∃numbers : ℕ→ℕ,NatAssign.Bank (Finset.Icc 311 332) numbers t.val ∧
         (∀k∈Finset.Icc 311 332,(numbers k).bits.length ≤ d 301) ∧ numbers 311=n 311) ∧
      WordCleanup.Bounded conversionRetiredWords (d 301) t.val ∧
      NatAssign.Bank CoefficientAllocation.workIds (CoefficientAllocation.allocatedWork cn) t.val ∧
      (∀k∈CoefficientAllocation.workIds,(CoefficientAllocation.allocatedWork cn k).bits.length ≤
        CoefficientAllocation.allocatedWorkWidth (CoefficientInput.joinWidth B)) ∧
      NatAssign.Bank AllocatedInverse.inactiveIds d t.val ∧
      (∀k∈AllocatedInverse.inactiveIds,(d k).bits.length ≤ InverseDescriptor.bankWidth q) ∧
      RationalAccumulator.Word t.val 376 (n 376) ∧
      WordCleanup.Bounded Horner.activeCleanup (W+(aliasArraySize (n 311)).bits.length) t.val ∧
      WordCleanup.Bounded SchurReadColumn.readoutWords (SchurReadColumn.readoutWidth D (n 311-3) W) t.val ∧
      BankArray.Scratch t.val ∧ RationalAccumulator.Blank t.val 7 ∧
      (∀i,(i<240 ∨ 384 ≤ i)→i<1200→(∀row,i≠SchurRow.output row column)→ out i=p i) ∧
      (∀k,6000≤k→t.val.tapes k=s.val.tapes k) ∧
      (∀k,850≤k→k<924→t.val.tapes k=s.val.tapes k) := by
  obtain ⟨c0,u,nf,coeff,snapshot,e0,b0,valid,ready,size,denominator,counter,index,retainedNaturals,retainedControls,retired,blank105,
      rawCells,working,workingWidth,allocatedWork,allocatedWidth,inactive,inactiveWidth,heapWord,decoded⟩ := BasisForcing.Inverse.executes column n extra cold v
    agree good B H I X hB hR hw ew cw hv ht hE hr input tape xs s hs he hcold hz h4 h7 h37
    h206 h216 oldOutput oldInput hword
  let cn:=CoefficientInput.joined n nf extra
  let Q:=CoefficientAllocation.budget cn
  let slot:=CoefficientAllocation.slotWidth Q
  let heap:=CoefficientAllocation.heap cn
  let q:=InverseDescriptor.selected (n 311) slot heap Q cold
  let d:=InverseDescriptor.values q
  let D:=SharedTable.denominator coeff
  let A:=AllocatedInverse.outputWidth (n 311) D d
  let W:=max A P
  have pkept : Cells SchurRow.bank p u.val := pcells.transfer_tapes (by
    intro k hk
    exact e0.protectsTape k (BasisForcing.Inverse.protectsTape column k (schur_ports k hk)))
  have sizeW : snapshot.data.Sized W := by
    rcases size with ⟨h1,h2,h3,h4,h5,h6,h7⟩
    have lo : A ≤ W := le_max_left _ _
    exact ⟨h1.trans lo,h2.trans lo,h3.trans lo,h4.trans lo,fun i=>(h5 i).trans lo,h6.trans lo,h7.trans lo⟩
  have quasi : (fun j : Fin 3=>(p (234+j.val)).value)=(fun j=>(RawFree.quasiParts v j).value) := by
    funext j
    rw [pquasi]
  have decodedP : ∀i:Fin (aliasArraySize (n 311)),
      ((Horner.channels snapshot.words 10 11).value i:ℚ)/(D:ℚ)^(n 311-2)=
        (cachedInverseApply (p 232).value (p 233).value (fun j=>(p (234+j.val)).value) (n 311)
          (rationalRightCoupling (rationalBasisField column)) (n 311-2)).get i := by
    simpa only [pzero,pone,quasi] using decoded
  obtain ⟨c1,t,out,e1,b1,output,validOut,widthOut,value,frame,middle,readout,scratch,seven,kept⟩ :=
    SchurReadColumn.executes_radius column (n 311) D W (InverseDescriptor.bankWidth q) snapshot d p hR
      (SharedTable.denominator_pos coeff (fun i=>(valid i).1)) sizeW workingWidth
      (fun i hi=>(pwidth i hi).mono (le_max_right _ _)) pgood decodedP input tape
      (aliasArraySize (n 311)).bits u (Snapshot.ready_mono ready (le_max_left _ _)) denominator counter
      working index blank105 pkept
  obtain ⟨raw,rawCells,rawWidth⟩:=rawCells
  have rawKept : Cells BasisForcing.bank raw t.val := rawCells.transfer_tapes (by
    intro k hk
    have bound:=source_ports k hk
    exact frame k bound.1 (fun h=>by have := schur_ports k h;omega))
  refine ⟨c0+c1,t,nf,D,out,raw,e0.seq e1,Nat.add_le_add b0 b1,
    output,validOut,widthOut,?_,rawKept,rawWidth,?_,?_,?_,?_,allocatedWidth,?_,inactiveWidth,
    RationalAccumulator.word_of_eq (middle 376 (by decide) (by decide) (by decide) (by decide)) heapWord,?_,readout,scratch,seven,kept,?_,?_⟩
  · intro row
    simpa only [pzero,pone,quasi] using value row
  · obtain ⟨numbers,bank,width⟩:=retainedNaturals
    refine ⟨numbers,?_,width⟩
    intro k hk
    apply RationalAccumulator.word_of_eq (middle k ?_ ?_ ?_ ?_) (bank k hk)
    all_goals simp only [Descriptors.retainedIds,Finset.mem_union,Finset.mem_Icc,
      Finset.mem_insert,Finset.mem_singleton] at hk;omega

  · obtain ⟨numbers,bank,width,radiusWord⟩:=retainedControls
    refine ⟨numbers,?_,width,radiusWord⟩
    intro k hk
    have bounds:=Finset.mem_Icc.mp hk
    exact RationalAccumulator.word_of_eq (middle k (by omega) (by omega) (by omega) (by omega)) (bank k hk)

  · intro k hk
    obtain ⟨bits,width,word⟩:=retired k hk
    refine ⟨bits,width,BankArray.word_of_eq (middle k ?_ ?_ ?_ ?_) word⟩
    all_goals simp only [conversionRetiredWords,retiredWords,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hk;omega

  · intro k hk
    apply RationalAccumulator.word_of_eq (middle k ?_ ?_ ?_ ?_) (allocatedWork k hk)
    all_goals simp only [CoefficientAllocation.workIds,Finset.mem_insert,Finset.mem_singleton] at hk;omega
  · intro k hk
    apply RationalAccumulator.word_of_eq (middle k ?_ ?_ ?_ ?_) (inactive k hk)
    all_goals simp only [AllocatedInverse.inactiveIds,Finset.mem_union,Finset.mem_Icc] at hk;omega

  · let C:=W+(aliasArraySize (n 311)).bits.length
    have sizeC : snapshot.data.Sized C := by
      obtain ⟨h1,h2,h3,h4,h5,h6,h7⟩:=sizeW
      have lo:W≤C:=Nat.le_add_right _ _
      exact ⟨h1.trans lo,h2.trans lo,h3.trans lo,h4.trans lo,fun i=>(h5 i).trans lo,h6.trans lo,h7.trans lo⟩
    have source:=Snapshot.Ready.bounded_active
      (Snapshot.ready_mono ready ((le_max_left A P).trans (Nat.le_add_right _ _))) sizeC (Nat.le_add_left _ _)
    intro k hk
    obtain ⟨bits,width,word⟩:=source k hk
    refine ⟨bits,width,BankArray.word_of_eq (middle k ?_ ?_ ?_ ?_) word⟩
    all_goals
      simp only [Horner.activeCleanup,Horner.workCleanup,Horner.portCleanup,List.mem_append,
        List.mem_cons,List.not_mem_nil,or_false,List.mem_range'_1] at hk
      omega

  · intro k high
    apply (frame k (by omega) ?_).trans
    · exact e0.protectsTape k (BasisForcing.Inverse.protectsTape column k (by omega))
    · intro member
      obtain ⟨i,member,cell⟩:=Finset.mem_biUnion.mp member
      have low : i<1371 := by
        simp only [SchurRow.bank,SchurRow.nodeCount_value,Finset.mem_union,Finset.mem_Ico] at member
        omega
      simp only [cellPorts,positivePort,negativePort,denominatorPort,
        Finset.mem_insert,Finset.mem_singleton] at cell
      omega

  · intro k lo hi
    exact (middle k (by omega) (by omega) (by omega) (by omega)).trans
      (e0.outsideTapes (BasisForcing.Inverse.edgeWorkspace_retained column) k lo hi)

#print axioms executes
end Maxwell.Continuum.Calibration.BasisSchurColumn
