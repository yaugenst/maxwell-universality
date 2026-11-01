import Maxwell.Continuum.CalibrationBasisCoefficientLayout
import Maxwell.Continuum.RationalDataflowRetainedCells
import Maxwell.Continuum.RationalDataflowBankInclusions

/-! A basis column generates its source and computes its coefficient storage
from measured runtime words. Both arrays start in arbitrary memory, and the
old traversal counter is cleared by the executed program. -/
namespace Maxwell.Continuum.Calibration.BasisForcing.CoefficientInput
open Maxwell.Cost Maxwell.Cost.Structured FreeFiber RationalDataflow PartArray ArrayDecodeMachine NeumannMachine
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384
attribute [local irreducible] bank sourceTable CoefficientAllocation.budget
  CoefficientAllocation.slotWidth CoefficientAllocation.slotOffset
  inputCost CoefficientAllocation.costBound allocationWidth metadataWidth workWidth prepareWidth

def joined (n nf extra : ℕ→ℕ) : ℕ→ℕ := numbers (n 311) (n 376) nf extra
  (PowerMachine.BufferNorm.Allocation.outputValues (allocationValues n))
def joinWidth (B : ℕ) : ℕ := prepareWidth (allocationWidth B)+B+workWidth B+metadataWidth B
def code (column : Fin 24) : Code := .seq (inputCode column) CoefficientAllocation.counterCode

private theorem output_headers {T M : ℕ} (a : Table T) (s : Store)
    (ready:a.OutputReady s) (hw:a.MetadataWidth M) :
    WordCleanup.Bounded PowerMachine.BufferNorm.Allocation.clearHeaders M s.val := by
  intro k hk
  simp only [PowerMachine.BufferNorm.Allocation.clearHeaders,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl
  · exact ⟨a.width,hw.width,ready.width⟩
  · exact ⟨a.basePositive,hw.basePositive,ready.basePositive⟩
  · exact ⟨a.baseNegative,hw.baseNegative,ready.baseNegative⟩
  · exact ⟨a.baseDenominator,hw.baseDenominator,ready.baseDenominator⟩
  · exact ⟨a.clock,hw.clock,ready.clock⟩

theorem executes (column : Fin 24) (n extra : ℕ→ℕ) (v : ℕ→Parts)
    (agree : ∀k∈ids bank,n k=dataValues v k) (good : Good bank v)
    (B H I : ℕ) (hB : 103≤B) (hR : 2≤n 311)
    (hw : ∀k∈allocationIds,(n k).bits.length≤B)
    (ew : ∀k∈extraIds,(extra k).bits.length≤B) (hv : ∀k∈retained,(v k).Width B)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (s : Store)
    (hs : NatAssign.Bank allocationIds n s.val) (he : NatAssign.Bank extraIds extra s.val)
    (hz : BankArray.Scratch s.val) (h4 : RationalAccumulator.Blank s.val 4)
    (h7 : RationalAccumulator.Blank s.val 7) (h37 : RationalAccumulator.Blank s.val 37)
    (h206 : RationalAccumulator.Blank s.val 206) (h216 : RationalAccumulator.Blank s.val 216)
    (oldOutput : WordCleanup.Bounded PowerMachine.BufferNorm.Allocation.clearHeaders H s.val)
    (oldInput : WordCleanup.Bounded Promote.headers I s.val) (hword : BankArray.Word s.val 201 xs) :
    ∃(cost : ℕ) (t : Store) (a : Table (aliasArraySize (n 311)))
        (b : Table (tableSize (aliasArraySize (n 311)))) (vf : ℕ→Parts) (nf : ℕ→ℕ),
      Executes input tape (code column) cost s t ∧
      cost ≤ inputCost (n 311) B H I xs.length+
        CoefficientAllocation.costBound (joined n nf extra) (joinWidth B) (metadataWidth B)+6*allocationWidth B+5 ∧
      a.Ready t ∧ b.OutputReady t ∧
      sameMetadata (sourceTable (n 311) (n 376) s.val.memory) a ∧
      addressValue b.width=CoefficientAllocation.slotWidth (CoefficientAllocation.budget (joined n nf extra)) ∧
      a.MetadataWidth (CoefficientAllocation.budget (joined n nf extra)) ∧
      b.MetadataWidth (CoefficientAllocation.metadataWidth (joinWidth B)) ∧
      b.Separated ∧ a.SeparatedFrom b ∧ SourceLayout b (CoefficientAllocation.heap (joined n nf extra)) ∧
      Good bank vf ∧ (∀k∈ids bank,nf k=dataValues vf k) ∧ nf 311=n 311 ∧
      (∀k∈retained,vf k=v k) ∧
      Cells bank vf t.val ∧ WidthBank bank (prepareWidth (allocationWidth B)) vf ∧
      NatAssign.Bank emissionIds (joined n nf extra) t.val ∧
      (∀k∈emissionIds,((joined n nf extra) k).bits.length≤CoefficientAllocation.budget (joined n nf extra)) ∧
      (∀i,(a.get i).Valid) ∧ tableSource (n 311) a=rationalRightCoupling (rationalBasisField column) ∧
      (∀k,k<5 → RationalAccumulator.Blank t.val k) ∧
      RationalAccumulator.Blank t.val 201 ∧ RationalAccumulator.Blank t.val 206 ∧ RationalAccumulator.Blank t.val 216 ∧
      RationalAccumulator.Word t.val 580 (CoefficientAllocation.budget (joined n nf extra)) ∧
      RationalAccumulator.Word t.val 570 (tableSize (aliasArraySize (n 311))) ∧
      RationalAccumulator.Word t.val 571 (CoefficientAllocation.slotWidth (CoefficientAllocation.budget (joined n nf extra))) ∧
      RationalAccumulator.Word t.val 572 (CoefficientAllocation.heap (joined n nf extra)) ∧
      NatAssign.Bank CoefficientAllocation.workIds (CoefficientAllocation.allocatedWork (joined n nf extra)) t.val ∧
      (∀k∈CoefficientAllocation.workIds,(CoefficientAllocation.allocatedWork (joined n nf extra) k).bits.length ≤
        CoefficientAllocation.allocatedWorkWidth (joinWidth B)) ∧
      t.val.inputHead=s.val.inputHead ∧ t.val.randomCursor=s.val.randomCursor ∧ t.val.output=s.val.output ∧
      (∀k∈continuationPorts,k≠216 → t.val.tapes k=s.val.tapes k) ∧
      RationalAccumulator.Word t.val 376 (n 376) := by
  obtain ⟨c0,u,a,vf,nf,word,e0,hc0,ready,out,metadata,metaB,g,nb,agrees,widths,keep,rad,zero,
    valid,value,count,len,ih,random,emitted,temp,cold,working,heapWord⟩:=
    input_executes column n v agree good B H I hB hR hw hv input tape xs s hs hz h4 h7 h37 h216 oldOutput oldInput hword
  have extraBank : NatAssign.Bank extraIds extra u.val := by
    intro k hk
    apply RationalAccumulator.word_of_eq (cold k (extra_inverse hk) _) (he k hk)
    simp only [extraIds,Finset.mem_union,Finset.mem_Icc] at hk
    omega
  have assembledBank:=assembled (n 311) (n 376) nf extra
    (PowerMachine.BufferNorm.Allocation.outputValues (allocationValues n)) rad
    (prepareWidth (allocationWidth B)) B (workWidth B) (metadataWidth B) widths ew
    (allocation_work_width n B hB hw) a s.val.memory metadata (sourceTable_metadata n B hB hw s.val.memory)
    u ready nb extraBank working
  have large:10≤joinWidth B:=by unfold joinWidth;omega
  obtain ⟨c1,t,e1,hc1,source,target,metaC,emission,budget,count1,width1,heap1,z201,z216,allocatedWork,allocatedWidth,frame⟩:=
    CoefficientAllocation.counter_executes (joined n nf extra) (joinWidth B) (metadataWidth B) large
      assembledBank.2 a input tape word u assembledBank.1 ready out.packing temp (output_headers a u out metaB) count
  have rawReady : Ready bank vf u := by
    refine ⟨?_,fun k hk=>zero k (by omega)⟩
    intro k hk
    rw [←agrees k hk]
    exact nb k (naturalIds_parts hk)
  have rawCells : Cells bank vf t.val := by
    apply (Cells.of_ready rawReady).transfer
    intro k hk
    apply frame.tapes
    simp only [CoefficientAllocation.counterChanged,CoefficientAllocation.changed,
      CoefficientAllocation.workChanged,PowerMachine.BufferNorm.Allocation.changed,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    omega
  have rawWidth : WidthBank bank (prepareWidth (allocationWidth B)) vf :=
    widthBank_of_naturals bank nf vf _ agrees (fun k hk=>widths k (naturalIds_parts hk))
  have preserved (k : ℕ) (hk:k∈continuationPorts) (hne:k≠216) : t.val.tapes k=s.val.tapes k := by
    have external:k∉CoefficientAllocation.counterChanged:=by
      simp only [continuationPorts,Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hk
      simp only [CoefficientAllocation.counterChanged,CoefficientAllocation.changed,
        CoefficientAllocation.workChanged,PowerMachine.BufferNorm.Allocation.changed,
        Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
      omega
    exact (frame.tapes k external).trans (cold k (Finset.mem_union_left _ hk) hne)
  refine ⟨c0+c1,t,a,CoefficientAllocation.table (joined n nf extra) u.val.memory,vf,nf,
    e0.seq e1,?_,source,target,metadata,coefficient_width _ _,?_,metaC,?_,?_,?_,g,agrees,rad,keep,rawCells,rawWidth,
    emission,(fun k hk=>CoefficientAllocation.budget_bound _ k (Finset.mem_union_left _ hk)),valid,value,?_,z201,
    RationalAccumulator.blank_of_eq (preserved 206 (by decide) (by decide)) h206,z216,
    budget,count1,width1,heap1,allocatedWork,allocatedWidth,frame.inputHead.trans ih,frame.randomCursor.trans random,frame.output.trans emitted,preserved,
    RationalAccumulator.word_of_eq (frame.tapes 376 (by decide)) heapWord⟩
  · exact (Nat.add_le_add hc0 hc1).trans (by omega)
  · exact source_metadata (n 311) (n 376) nf extra _ s.val.memory a metadata
  · exact coefficient_separated _ _
  · exact separated (n 311) (n 376) nf extra _ s.val.memory u.val.memory a metadata
  · exact coefficient_layout _ _
  · intro k hk
    by_cases h:k<4
    · interval_cases k
      · exact source.scratch.1
      · exact source.scratch.2.1
      · exact source.scratch.2.2.1
      · exact source.scratch.2.2.2.1
    · have eq:k=4:=by omega
      subst k
      exact RationalAccumulator.blank_of_eq (frame.tapes 4 (by decide)) (zero 4 (by decide))

#print axioms executes
end Maxwell.Continuum.Calibration.BasisForcing.CoefficientInput
