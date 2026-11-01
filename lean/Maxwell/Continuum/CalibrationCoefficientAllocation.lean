import Maxwell.Continuum.CalibrationCoefficientAllocationBounds
import Maxwell.Continuum.RationalDataflowArrayTransfer

/-! Executed coefficient allocation: scan the actual source words, calculate
all destination metadata, and construct its width clock over arbitrary memory.
The existing source array and all emission inputs are retained. -/
namespace Maxwell.Continuum.Calibration.CoefficientAllocation
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray ArrayDecodeMachine NeumannMachine
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 2048
attribute [local irreducible] measured planned sources slotWidth slotOffset

def workChanged : Finset ℕ := {0,1,2,3,570,571,572,573,580,581,582,583,584}
def changed : Finset ℕ := workChanged∪PowerMachine.BufferNorm.Allocation.changed
def code : Code := .seq measureCode (.seq (NatAssign.code plan) PowerMachine.BufferNorm.Allocation.code)
def costBound (n : ℕ→ℕ) (B H : ℕ) : ℕ :=
  (192000*(B+2)^2+sources.length*(200000*(B+626+sources.length*B+2)^2)+1)+
  3000*8^22*(measureWidth B+1002)^2+
  2^60*(planWidth B+H+slotWidth (budget n)+3)^2

def allocatedWork (n : ℕ→ℕ) (k : ℕ) : ℕ :=
  if k=573 then PowerMachine.BufferNorm.Allocation.outputValues (planned n) k else planned n k
def allocatedWorkWidth (B : ℕ) : ℕ := 2^8*(planWidth B+1)

def table (n : ℕ→ℕ) (memory : ℕ→Bool) : Table (tableSize (aliasArraySize (n 311))) :=
  Profile.Runtime.memoryTable _ (slotWidth (budget n)) (heap n) (slotWidth_pos _) memory

theorem executes (n : ℕ→ℕ) (B H : ℕ) (hB : 10≤B) (hw : ∀k∈allIds,(n k).bits.length≤B)
    (a : Table (aliasArraySize (n 311)))
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : NatAssign.Bank allIds n s.val)
    (ha : a.Ready s) (h37 : RationalAccumulator.Blank s.val 37) (h216 : RationalAccumulator.Blank s.val 216)
    (headers : WordCleanup.Bounded PowerMachine.BufferNorm.Allocation.clearHeaders H s.val) :
    ∃cost t,Executes input tape code cost s t ∧ cost≤costBound n B H ∧
      a.Ready t ∧ (table n s.val.memory).OutputReady t ∧
      (table n s.val.memory).MetadataWidth (metadataWidth B) ∧
      NatAssign.Bank emissionIds n t.val ∧ RationalAccumulator.Word t.val 580 (budget n) ∧
      RationalAccumulator.Word t.val 570 (tableSize (aliasArraySize (n 311))) ∧
      RationalAccumulator.Word t.val 571 (slotWidth (budget n)) ∧ RationalAccumulator.Word t.val 572 (heap n) ∧
      RationalAccumulator.Blank t.val 216 ∧
      NatAssign.Bank workIds (allocatedWork n) t.val ∧
      (∀k∈workIds,(allocatedWork n k).bits.length ≤ allocatedWorkWidth B) ∧
      BinaryPrecision.Frame changed s.val t.val := by
  obtain ⟨c0,u,e0,hc0,rawBank0,z0,f0⟩ := NatAssign.LengthSum.initialized_executes allIds allIds_ge 580 581 626
    (by decide) (by decide) (by decide) sources sources_valid n B hw
    (by simpa only [show (626:ℕ).bits.length=10 by decide] using hB)
    input tape s hs (fun k hk=>by
      interval_cases k
      · exact ha.scratch.1
      · exact ha.scratch.2.1
      · exact ha.scratch.2.2.1
      · exact ha.scratch.2.2.2.1)
  have b0 : NatAssign.Bank allIds (measured n) u.val := by
    simpa only [measured] using rawBank0
  obtain ⟨c1,u1,e1,hc1,rawBank1,z1,f1⟩ := NatAssign.executes allIds allIds_ge plan plan_valid (measured n)
    input tape u b0 z0
  have b1 : NatAssign.Bank allIds (planned n) u1.val := by
    simpa only [planned] using rawBank1
  have price:=NatAssign.price_bound allIds plan plan_valid (measured n) (measureWidth B+1000)
    (fun k hk=>(measured_width n B hw k hk).trans (Nat.le_add_right _ _)) (plan_literals B)
  change NatAssign.price plan (measured n)≤3000*8^22*(measureWidth B+1002)^2 at price
  have frame0 : BinaryPrecision.Frame workChanged s.val u1.val :=
    (f0.mono (by decide)).trans (f1.mono (by decide))
  have scratch : BankArray.Scratch u1.val :=
    ⟨z1 0 (by decide),z1 1 (by decide),z1 2 (by decide),z1 3 (by decide),
      RationalAccumulator.blank_of_eq (frame0.tapes 5 (by decide)) ha.scratch.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (frame0.tapes 6 (by decide)) ha.scratch.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (frame0.tapes 8 (by decide)) ha.scratch.2.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (frame0.tapes 9 (by decide)) ha.scratch.2.2.2.2.2.2.2⟩
  have inputs : PowerMachine.BufferNorm.Allocation.inputs⊆allIds := by decide
  have headers1 : WordCleanup.Bounded PowerMachine.BufferNorm.Allocation.clearHeaders H u1.val := by
    intro k hk
    obtain ⟨xs,hlen,word⟩:=headers k hk
    have outside:k∉workChanged:=by
      simp only [PowerMachine.BufferNorm.Allocation.clearHeaders,List.mem_cons,List.not_mem_nil,or_false] at hk
      simp only [workChanged,Finset.mem_insert,Finset.mem_singleton]
      omega
    exact ⟨xs,hlen,BankArray.word_of_eq (frame0.tapes k outside) word⟩
  have positive : 0<planned n 571 := by rw [(plan_outputs n).2.1];exact slotWidth_pos _
  obtain ⟨c2,t,e2,hc2,out,allocatedBank,temp,f2⟩ := PowerMachine.BufferNorm.Allocation.executes (planned n)
    (planWidth B) H positive (fun k hk=>planned_width n B hw k (inputs hk)) input tape u1
    (fun k hk=>b1 k (inputs hk)) scratch
    (RationalAccumulator.blank_of_eq (frame0.tapes 7 (by decide)) ha.seven)
    (RationalAccumulator.blank_of_eq (frame0.tapes 37 (by decide)) h37)
    (RationalAccumulator.blank_of_eq (frame0.tapes 216 (by decide)) h216) headers1
  have output : (table n s.val.memory).OutputReady t := by
    have transfer (m w base : ℕ) (hp : 0<w) (hm:m=tableSize (aliasArraySize (n 311)))
        (hwidth:w=slotWidth (budget n)) (hheap:base=heap n)
        (h:(Profile.Runtime.memoryTable m w base hp u1.val.memory).OutputReady t) :
        (table n s.val.memory).OutputReady t := by
      subst m;subst w;subst base
      simpa only [table,frame0.memory] using h
    exact transfer _ _ _ positive (plan_outputs n).1 (plan_outputs n).2.1 (plan_outputs n).2.2.1 out
  have frame : BinaryPrecision.Frame changed s.val t.val :=
    (frame0.mono (Finset.subset_union_left)).trans (f2.mono (Finset.subset_union_right))
  have ready : a.Ready t := ha.transfer frame.memory (by
    intro k hk
    apply frame.tapes k
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    simp only [changed,workChanged,PowerMachine.BufferNorm.Allocation.changed,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    omega) output.scratch output.seven
  have bank : NatAssign.Bank emissionIds n t.val := by
    intro k hk
    have external:k∉changed:=fun hc=>Finset.disjoint_left.mp
      (show Disjoint emissionIds changed by decide) hk hc
    exact RationalAccumulator.word_of_eq (frame.tapes k external)
      (hs k (Finset.mem_union_left _ (Finset.mem_union_left _ hk)))
  have retained (k : ℕ) (hk:k∈({570,571,572,580}:Finset ℕ)) :
      RationalAccumulator.Word t.val k (planned n k) := by
    have member:k∈workIds:=by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hk
      simp only [workIds,Finset.mem_insert,Finset.mem_singleton]
      omega
    have external:k∉PowerMachine.BufferNorm.Allocation.changed:=by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hk
      simp only [PowerMachine.BufferNorm.Allocation.changed,Finset.mem_insert,Finset.mem_singleton]
      omega
    exact RationalAccumulator.word_of_eq (f2.tapes k external) (b1 k (Finset.mem_union_right sourceIds member))
  have measured580 : planned n 580=budget n := by
    rw [planned,NatAssign.values_preserves,measured_budget]
    simp [plan,NatAssign.Instruction.target]
  have workBank : NatAssign.Bank workIds (allocatedWork n) t.val := by
    intro k hk
    by_cases eq:k=573
    · subst k
      exact allocatedBank 573 (by decide)
    · rw [allocatedWork,ite_eq_right eq]
      apply RationalAccumulator.word_of_eq (f2.tapes k ?_) (b1 k (Finset.mem_union_right _ hk))
      simp only [workIds,Finset.mem_insert,Finset.mem_singleton] at hk
      simp only [PowerMachine.BufferNorm.Allocation.changed,Finset.mem_insert,Finset.mem_singleton]
      omega
  have workWidth : ∀k∈workIds,(allocatedWork n k).bits.length ≤ allocatedWorkWidth B := by
    intro k hk
    by_cases eq:k=573
    · subst k
      rw [allocatedWork,ite_eq_left (rfl : (573:ℕ)=573)]
      have h:=NatAssign.values_width_bound PowerMachine.BufferNorm.Allocation.ids
        PowerMachine.BufferNorm.Allocation.plan PowerMachine.BufferNorm.Allocation.valid _ (planWidth B)
        (PowerMachine.BufferNorm.Allocation.cleared_width _ _
          (fun i hi=>planned_width n B hw i (inputs hi)))
        (by simp [PowerMachine.BufferNorm.Allocation.plan,NatAssign.Instruction.literalWidth])
        573 (by decide)
      change (PowerMachine.BufferNorm.Allocation.outputValues (planned n) 573).bits.length+1 ≤ allocatedWorkWidth B at h
      omega
    · rw [allocatedWork,ite_eq_right eq]
      exact (planned_width n B hw k (Finset.mem_union_right _ hk)).trans (by unfold allocatedWorkWidth;omega)
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,ready,output,table_metadata n B hw _,bank,
    by simpa only [measured580] using retained 580 (by decide),
    by simpa only [(plan_outputs n).1] using retained 570 (by decide),
    by simpa only [(plan_outputs n).2.1] using retained 571 (by decide),
    by simpa only [(plan_outputs n).2.2.1] using retained 572 (by decide),temp,workBank,workWidth,frame⟩
  rw [(plan_outputs n).2.1] at hc2
  unfold costBound
  omega

#print axioms executes
end Maxwell.Continuum.Calibration.CoefficientAllocation
