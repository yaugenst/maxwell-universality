import Maxwell.Continuum.CalibrationGeneratedInverseRetained
import Maxwell.Continuum.CalibrationInverseDescriptorReady

/-! A generated coefficient destination supplies every inverse descriptor.
The actual countdown and wider shared array are computed before coefficient
generation and cached inversion; no descriptor or inverse snapshot is given. -/
namespace Maxwell.Continuum.Calibration.AllocatedInverse
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open RationalDataflow PartArray ArrayDecodeMachine NeumannMachine
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

def persistentPorts : Finset ℕ := insert 376 (Finset.Icc 570 584)
def inactiveIds : Finset ℕ := Finset.Icc 116 119∪Finset.Icc 134 139

def code : Code := .seq InverseDescriptor.startCode generatedInverseCode
def inverseCost (R B W BN slot D : ℕ) (d : ℕ→ℕ) : ℕ :=
  generatedCoefficientCost R B W+256*(B+W+1)+
    inversePrepareCost (coefficientWidth (countWidth B)) BN B (d 301)
      (coefficientBaseWidth (countWidth B)) (tableSize (aliasArraySize R))+
    convertedCost (aliasArraySize R) (d 301) (d 302) D (d 304)
      W (continuationBudget W BN) slot (tableSize (aliasArraySize R)).bits.length
def outputWidth (R D : ℕ) (d : ℕ→ℕ) : ℕ :=
  initializedWidth (aliasArraySize R) (d 301) (d 302) D (d 304) (d 301)

theorem executes (R base B slot X M : ℕ) (hR:3≤R) (hB:101≤B)
    (a : Table (aliasArraySize R)) (b : Table (tableSize (aliasArraySize R)))
    (v : ℕ→Parts) (natural cold : ℕ→ℕ)
    (hn:∀k∈ids RawFree.neighborRegisters,natural k=dataValues v k)
    (hw:∀k∈emissionIds,(natural k).bits.length≤B)
    (hp:∀k∈matrixParameters,(v k).Width B ∧ (v k).Valid) (radius:natural 311=R)
    (hc:∀k∈InverseDescriptor.coldIds,(cold k).bits.length≤X)
    (aValid:∀i,(a.get i).Valid) (aMeta:a.MetadataWidth B) (bMeta:b.MetadataWidth M)
    (layout:SourceLayout b base) (width:addressValue b.width=slot)
    (fit:coefficientWidth (countWidth B)≤slot) (separated:b.Separated) (disjoint:a.SeparatedFrom b)
    (ht:(3:ℝ)≤(v 0).value) (hE:(7:ℝ)≤(v 1).value ∧ ((v 1).value:ℝ)≤8)
    (hr:∀k,|((RawFree.quasiParts v k).value:ℝ)|≤1/16)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (source:a.Ready s) (target:b.OutputReady s) (bank:NatAssign.Bank emissionIds natural s.val)
    (coldBank:NatAssign.Bank InverseDescriptor.coldIds cold s.val)
    (zero:∀k,k<5→RationalAccumulator.Blank s.val k)
    (z201:RationalAccumulator.Blank s.val 201) (z206:RationalAccumulator.Blank s.val 206)
    (z216:RationalAccumulator.Blank s.val 216)
    (count:RationalAccumulator.Word s.val 570 (tableSize (aliasArraySize R)))
    (slotWord:RationalAccumulator.Word s.val 571 slot) (baseWord:RationalAccumulator.Word s.val 572 base)
    (budgetWord:RationalAccumulator.Word s.val 580 B) :
    let q:=InverseDescriptor.selected R slot base B cold
    let d:=InverseDescriptor.values q
    ∃(cost : ℕ) (t : Store) (coeff : CoefficientIndex (aliasArraySize R)→Parts) (out : Snapshot (aliasArraySize R)),
      Executes input tape code cost s t ∧
      cost≤InverseDescriptor.startCost (InverseDescriptor.inputs R slot base B cold)
        (InverseDescriptor.inputBound R slot base B X M)+
        inverseCost R B (InverseDescriptor.rawWidth q) (InverseDescriptor.bankWidth q) slot (SharedTable.denominator coeff) d ∧
      (∀i,(coeff i).Valid ∧ (coeff i).Width (InverseDescriptor.rawWidth q) ∧
        (coeff i).value=cachedCoefficientTable (v 0).value (v 1).value
          (fun j=>(RawFree.quasiParts v j).value) R (tableSource R a) i) ∧
      out.Ready (aliasArraySize R).bits (outputWidth R (SharedTable.denominator coeff) d) t.val ∧
      out.data.Sized (outputWidth R (SharedTable.denominator coeff) d) ∧
      RationalAccumulator.Word t.val 126 (SharedTable.denominator coeff) ∧
      RationalAccumulator.Word t.val 304 (R-3) ∧
      RationalAccumulator.Blank t.val 140 ∧
      (∃numbers : ℕ→ℕ,NatAssign.Bank Descriptors.retainedIds numbers t.val ∧
        ∀k∈Descriptors.retainedIds,(numbers k).bits.length ≤ Descriptors.retainedWidth (d 301)) ∧
      (∃numbers : ℕ→ℕ,NatAssign.Bank (Finset.Icc 311 332) numbers t.val ∧
         (∀k∈Finset.Icc 311 332,(numbers k).bits.length ≤ d 301) ∧ numbers 311=R) ∧
      WordCleanup.Bounded conversionRetiredWords (d 301) t.val ∧
      RationalAccumulator.Blank t.val 105 ∧
      (∃raw : ℕ→Parts,Cells RawFree.neighborRegisters raw t.val ∧
        WidthBank RawFree.neighborRegisters (d 301) raw) ∧
      NatAssign.Bank (Finset.Icc 530 534) d t.val ∧
      (∀k∈Finset.Icc 530 534,(d k).bits.length≤InverseDescriptor.bankWidth q) ∧
      (∀k∈persistentPorts,t.val.tapes k=s.val.tapes k) ∧
      NatAssign.Bank inactiveIds d t.val ∧
      (∀k∈inactiveIds,(d k).bits.length ≤ InverseDescriptor.bankWidth q) ∧
      ∀i:Fin (aliasArraySize R),((Horner.channels out.words 10 11).value i:ℚ)/(SharedTable.denominator coeff:ℚ)^(R-2)=
        (cachedInverseApply (v 0).value (v 1).value (fun j=>(RawFree.quasiParts v j).value)
          R (tableSource R a) (R-2)).get i := by
  dsimp only
  let n:=InverseDescriptor.inputs R slot base B cold
  let q:=InverseDescriptor.selected R slot base B cold
  let d:=InverseDescriptor.values q
  let W:=InverseDescriptor.rawWidth q
  let BN:=InverseDescriptor.bankWidth q
  let IB:=InverseDescriptor.inputBound R slot base B X M
  have assembled:=InverseDescriptor.input_bank R slot base B X M cold b layout width bMeta s target coldBank hc
    (by simpa only [radius] using bank 311 (by decide)) count slotWord baseWord budgetWord
  obtain ⟨c0,u,e0,hc0,bu,zu,wu,frame⟩:=InverseDescriptor.start_executes n IB
    (by unfold IB InverseDescriptor.inputBound;omega)
    (by simpa only [n,(InverseDescriptor.input_parameters R slot base B cold).1] using hR)
    assembled.2 input tape s assembled.1 (fun k hk=>zero k (by omega))
  have descriptorBank:NatAssign.Bank InverseDescriptor.ids d u.val:=bu
  have descriptorWidth:∀k∈InverseDescriptor.ids,(d k).bits.length≤BN:=wu
  have arrays:=InverseDescriptor.ready_transfer a b s u source target zu frame
  have emission:NatAssign.Bank emissionIds natural u.val:=by
    intro k hk
    exact RationalAccumulator.word_of_eq (frame.tapes k (fun h=>
      Finset.disjoint_left.mp (show Disjoint emissionIds InverseDescriptor.startChanged by decide) hk h)) (bank k hk)
  have blanks:∀k,k<5→RationalAccumulator.Blank u.val k:=by
    intro k hk
    by_cases h:k<4
    · exact zu k h
    · have h4:k=4:=by omega
      subst k
      exact RationalAccumulator.blank_of_eq (frame.tapes 4 (by decide)) (zero 4 (by decide))
  have dim:d 300=aliasArraySize R:=by
    dsimp only [d]
    rw [(InverseDescriptor.outputs q).1]
    exact InverseDescriptor.selected_dimension R slot base B cold
  have iter:d 304=R-3:=by
    dsimp only [d]
    rw [(InverseDescriptor.outputs q).2.2.2.1]
    exact (InverseDescriptor.selected_parameters R slot base B cold).2.2.2.2
  have inputIds:Finset.Icc 300 309⊆InverseDescriptor.ids:=by decide
  have unusedIds:Finset.Icc 107 140⊆InverseDescriptor.ids:=by decide
  have heapRoom:base+3*tableSize (aliasArraySize R)*addressValue b.width≤d 302:=by
    dsimp only [d]
    rw [width,(InverseDescriptor.outputs q).2.2.1,InverseDescriptor.selected_heap]
  have shared:PartArray.sharedWidth (tableSize (aliasArraySize R)) W≤continuationBudget W BN:=by
    have h:=InverseDescriptor.shared q
    simpa only [q,(InverseDescriptor.selected_parameters R slot base B cold).2.1] using h
  have arith:commonWidth (aliasArraySize R) (d 304) (W+1)≤d 301:=by
    simpa only [q,InverseDescriptor.selected_dimension] using InverseDescriptor.arithmetic q
  have address:(d 302).bits.length+2*(aliasArraySize R).bits.length+(d 301).bits.length+10≤d 301:=by
    simpa only [q,InverseDescriptor.selected_dimension] using InverseDescriptor.address q
  have counter:BankArray.Word u.val 201 []:=by
    change RationalAccumulator.Word u.val 201 0
    rw [RationalAccumulator.zero_word_iff_blank]
    exact RationalAccumulator.blank_of_eq (frame.tapes 201 (by decide)) z201
  obtain ⟨c1,t,coeff,out,e1,hc1,valid,ready,sized,denominator,counter1,blank,retained,controls,retired,blank105,rawCells,coldFrame,result⟩:=
    generated_inverse_executes R a b base B W BN hB v natural d d hn hw hp radius dim
      (fun k hk=>descriptorWidth k (inputIds hk)) (fun k hk=>descriptorWidth k (unusedIds hk)) aValid aMeta
      (InverseDescriptor.selected_metadata R slot base B cold b layout width) (by simpa only [width] using fit)
      separated disjoint layout heapRoom shared (InverseDescriptor.prepare q) arith address ht hE hr
      input tape [] (by simp) u emission (fun k hk=>descriptorBank k (inputIds hk))
      (fun k hk=>descriptorBank k (unusedIds hk)) blanks arrays.1 arrays.2 counter
      (RationalAccumulator.blank_of_eq (frame.tapes 206 (by decide)) z206)
      (RationalAccumulator.blank_of_eq (frame.tapes 216 (by decide)) z216)
  have steps:d 304+1=R-2:=by omega
  refine ⟨c0+c1,t,coeff,out,e0.seq e1,?_,valid,ready,sized,denominator,?_,blank,retained,controls,retired,blank105,rawCells,?_,?_,?_,?_,?_,?_⟩
  · rw [width] at hc1
    exact Nat.add_le_add hc0 hc1
  · simpa only [iter] using counter1
  · intro k hk
    exact RationalAccumulator.word_of_eq (coldFrame k hk)
      (descriptorBank k ((by decide : Finset.Icc 530 534⊆InverseDescriptor.ids) hk))
  · intro k hk
    exact descriptorWidth k ((by decide : Finset.Icc 530 534⊆InverseDescriptor.ids) hk)
  · intro k hk
    apply (e1.protectsSet inverseRetainedPorts generatedInverse_retained k
      ((by decide : persistentPorts⊆inverseRetainedPorts) hk)).trans (frame.tapes k ?_)
    simp only [persistentPorts,Finset.mem_insert,Finset.mem_Icc] at hk
    simp only [InverseDescriptor.startChanged,InverseDescriptor.changed,Finset.mem_insert,Finset.mem_singleton]
    omega
  · intro k hk
    have member : k∈InverseDescriptor.ids := (by decide : inactiveIds⊆InverseDescriptor.ids) hk
    exact RationalAccumulator.word_of_eq
      (e1.protectsSet inverseRetainedPorts generatedInverse_retained k
        ((by decide : inactiveIds⊆inverseRetainedPorts) hk)) (descriptorBank k member)
  · intro k hk
    exact descriptorWidth k ((by decide : inactiveIds⊆InverseDescriptor.ids) hk)
  · intro i
    simpa only [steps] using result i

#print axioms executes
end Maxwell.Continuum.Calibration.AllocatedInverse
