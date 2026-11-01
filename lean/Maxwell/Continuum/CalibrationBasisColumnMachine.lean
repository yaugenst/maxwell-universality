import Maxwell.Continuum.CalibrationBasisColumnState

/-! One fixed source/inverse/Schur computation followed by its charged
restart. The returned state is the actual input boundary for another column. -/
namespace Maxwell.Continuum.Calibration.BasisColumn
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open RationalDataflow PartArray ArrayDecodeMachine NeumannMachine BasisForcing
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384
attribute [local irreducible] BasisForcing.bank SchurRow.nodeCount
  CoefficientAllocation.budget CoefficientAllocation.slotWidth CoefficientAllocation.slotOffset
  allocationWidth prepareWidth SchurReadColumn.workingWidth SchurColumn.resultWidth
  SchurReadColumn.rows AllocatedInverse.outputWidth InverseDescriptor.bankWidth
  Descriptors.retainedWidth CoefficientAllocation.allocatedWorkWidth CoefficientInput.joinWidth

def code (column : Fin 24) : Code := .seq (BasisSchurColumn.code column) BasisReentry.code

theorem executes (column : Fin 24) (R heap P : ℕ) (p : ℕ→Parts)
    (radius : 3≤R) (physical : admissible p)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (state : State R heap P p s) :
    ∃cost t out Q,Executes input tape (code column) cost s t ∧ State R heap Q out t ∧
      (∀row,(out (SchurRow.output row column)).value=matrix R p row column) ∧
      (∀i,(i<240 ∨ 384 ≤ i)→i<1200→(∀row,i≠SchurRow.output row column)→ out i=p i) ∧
      (∀k,6000≤k→t.val.tapes k=s.val.tapes k) ∧
      (∀k,850≤k→k<924→t.val.tapes k=s.val.tapes k) := by
  let n:=BasisReentry.numbers R heap p
  let v:=BasisScalarReload.values p
  let B:=inputWidth R heap P
  have large : 103≤B := by unfold B inputWidth;omega
  have rad : n 311=R := BasisReentry.radius R heap p
  have free : n 376=heap := BasisReentry.heap R heap p
  have sourceGood : Good BasisForcing.bank v := fun i hi=>state.good i (Finset.mem_union_left _ hi)
  have sourceWidth : ∀i∈retained,(v i).Width B := by
    intro i hi
    exact (state.width i (Finset.mem_union_left _ (source_mem i hi))).mono (by unfold B inputWidth;omega)
  have zero:=BasisScalarReload.source_values p
  have quasi : (fun j=>(RawFree.quasiParts v j).value)=(fun j:Fin 3=>(p (234+j.val)).value) := by
    funext j
    rw [quasi_values]
  obtain ⟨c0,u,nf,D,out,raw,e0,b0,ready,good,width,value,rawCells,rawWidth,
      descriptors,controls,retired,allocator,allocatorWidth,inactive,inactiveWidth,heapWord,
      active,readout,scratch,seven,kept,high,interval⟩:=BasisSchurColumn.executes column n (fun _=>0) (fun _=>0) v
    (BasisReentry.numbers_agree R heap p) sourceGood B 0 0 0 large (by omega)
    state.natural_width (by intro k _;exact Nat.zero_le _) (by intro k _;exact Nat.zero_le _)
    sourceWidth (by simpa only [v,zero.1] using physical.1)
    (by simpa only [v,zero.2.1] using And.intro physical.2.1 physical.2.2.1)
    (by intro j;simpa only [v,quasi_values] using physical.2.2.2 j)
    input tape [] s state.ready.naturals state.ready.extra state.ready.cold state.ready.scratch
    state.ready.four state.ready.seven state.ready.packing state.ready.inputTemp state.ready.outputTemp
    state.ready.outputHeaders state.ready.inputHeaders state.ready.counter
    p P state.schur_width state.schur_good zero.1.symm zero.2.1.symm
    (fun j=>(quasi_values p j).symm) state.schur_cells
  let cn:=CoefficientInput.joined n nf (fun _=>0)
  let q:=InverseDescriptor.selected R (CoefficientAllocation.slotWidth (CoefficientAllocation.budget cn))
    (CoefficientAllocation.heap cn) (CoefficientAllocation.budget cn) (fun _=>0)
  let d:=InverseDescriptor.values q
  let W:=max (AllocatedInverse.outputWidth R D d) P
  let M:=Descriptors.retainedWidth (d 301)+(d 301)+(d 301)+
    CoefficientAllocation.allocatedWorkWidth (CoefficientInput.joinWidth B)+InverseDescriptor.bankWidth q+
    (W+(aliasArraySize R).bits.length)+SchurReadColumn.readoutWidth D (R-3) W
  let oldB:=max (d 301) (prepareWidth (allocationWidth B))
  let outP:=SchurColumn.resultWidth SchurReadColumn.rows (SchurReadColumn.workingWidth D (R-3) W)
  have bounded : WordCleanup.Bounded BasisReentry.cleanupWords M u.val := by
    apply BasisReentry.cleanup_bounded u (Descriptors.retainedWidth (d 301)) (d 301) (d 301)
      (CoefficientAllocation.allocatedWorkWidth (CoefficientInput.joinWidth B)) (InverseDescriptor.bankWidth q)
      (W+(aliasArraySize R).bits.length) (SchurReadColumn.readoutWidth D (R-3) W)
    · simpa only [q,cn,d,rad] using descriptors
    · obtain ⟨a,bank,bound,_⟩:=controls
      exact ⟨a,bank,by simpa only [q,cn,d,rad] using bound⟩
    · simpa only [q,cn,d,rad] using retired
    · exact ⟨CoefficientAllocation.allocatedWork cn,allocator,allocatorWidth⟩
    · exact ⟨d,by simpa only [d,q,cn,rad] using inactive,
        by simpa only [d,q,cn,rad] using inactiveWidth⟩
    · simpa only [W,d,q,cn,rad] using active
    · simpa only [W,d,q,cn,rad] using readout
  have radiusWord : RationalAccumulator.Word u.val 311 R := by
    obtain ⟨a,bank,_,equal⟩:=controls
    simpa only [equal,rad] using bank 311 (by decide)
  have positive : 1≤oldB := by
    have bound:0<prepareWidth (allocationWidth B) := by unfold prepareWidth;positivity
    exact bound.trans_le (le_max_right _ _)
  obtain ⟨c1,t,e1,b1,canonical,valid,finalWidth,frame⟩:=BasisReentry.executes R heap M oldB outP raw out
    positive (by simpa only [oldB,d,q,cn,rad] using rawWidth)
    (by simpa only [outP,W,d,q,cn,rad] using width) good input tape u bounded rawCells ready
    radiusWord (by simpa only [free] using heapWord) scratch seven
  refine ⟨c0+c1,t,out,max 1 outP,e0.seq e1,⟨canonical,valid,finalWidth⟩,?_,kept,?_,?_⟩
  · intro row
    simpa only [matrix,rad,v,zero.1,zero.2.1,quasi] using value row
  · intro k hk
    apply (frame.tapes k ?_).trans (high k hk)
    intro member
    have := BasisReentry.changed_bound k member
    omega

  · intro k lo hi
    exact (frame.tapes k (BasisReentry.changed_middle k (by omega) (by omega))).trans (interval k lo hi)

#print axioms executes
end Maxwell.Continuum.Calibration.BasisColumn
