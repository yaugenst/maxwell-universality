import Maxwell.Continuum.RationalDataflowArrayNormalizeAllocationBounds

/-! The actual normalization allocator scans the retained input words,
computes capacity and addresses, writes the destination descriptor and clock,
and restores both copies of the runtime entry count. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray.Normalize.Allocation
open Maxwell.Cost Maxwell.Cost.Structured Calibration
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
attribute [local irreducible] measured planned sources Profile.Runtime.memoryTable

def workChanged : Finset ℕ := {0,1,2,3}∪workIds
def changed : Finset ℕ := workChanged∪PowerMachine.BufferNorm.Allocation.changed
def code : Code := .seq measureCode (.seq (NatAssign.code plan) PowerMachine.BufferNorm.Allocation.code)
def costBound (n : ℕ→ℕ) (B H : ℕ) : ℕ :=
  (192000*(B+2)^2+sources.length*(200000*(B+1000+sources.length*B+2)^2)+1)+
  3000*8^plan.length*(measureWidth B+8)^2+2^60*(planWidth B+H+capacity n+3)^2

theorem executes {T : ℕ} (a : Table T) (n : ℕ→ℕ) (v : ℕ→Parts)
    (B H : ℕ) (hB : 10≤B) (width : ∀k∈allIds,(n k).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank allIds n s.val) (array : a.Ready s) (raw : Ready slots v s)
    (h37 : RationalAccumulator.Blank s.val 37) (h216 : RationalAccumulator.Blank s.val 216)
    (headers : WordCleanup.Bounded PowerMachine.BufferNorm.Allocation.clearHeaders H s.val) :
    ∃cost t,Executes input tape code cost s t ∧ cost≤costBound n B H ∧
      a.Ready t ∧ Ready slots v t ∧ (table n s.val.memory).OutputReady t ∧
      NatAssign.Bank sourceIds n t.val ∧ RationalAccumulator.Word t.val 802 (budget n) ∧
      RationalAccumulator.Word t.val 201 (n 788) ∧ RationalAccumulator.Word t.val 787 (n 788) ∧
      RationalAccumulator.Word t.val 574 (heapEnd n) ∧ RationalAccumulator.Blank t.val 216 ∧
      BinaryPrecision.Frame changed s.val t.val := by
  obtain ⟨c0,u,e0,h0,b0,z0,f0⟩ := NatAssign.LengthSum.initialized_executes allIds allIds_ge
    802 803 1000 (by decide) (by decide) (by decide) sources sources_valid n B width
    (by simpa only [show (1000:ℕ).bits.length=10 by decide] using hB)
    input tape s bank raw.2
  have bank0 : NatAssign.Bank allIds (measured n) u.val := by simpa only [measured] using b0
  obtain ⟨c1,w,e1,h1,b1,z1,f1⟩ := NatAssign.executes allIds allIds_ge plan plan_valid
    (measured n) input tape u bank0 z0
  have bank1 : NatAssign.Bank allIds (planned n) w.val := by simpa only [planned] using b1
  have price:=NatAssign.price_bound allIds plan plan_valid (measured n) (measureWidth B+6)
    (fun k hk=>(measured_width n B width k hk).trans (Nat.le_add_right _ _)) (plan_literals B)
  norm_num only [Nat.add_assoc] at price
  have frame0 : BinaryPrecision.Frame workChanged s.val w.val :=
    (f0.mono (by decide)).trans (f1.mono (by decide))
  have scratch : BankArray.Scratch w.val :=
    ⟨z1 0 (by decide),z1 1 (by decide),z1 2 (by decide),z1 3 (by decide),
      RationalAccumulator.blank_of_eq (frame0.tapes 5 (by decide)) array.scratch.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (frame0.tapes 6 (by decide)) array.scratch.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (frame0.tapes 8 (by decide)) array.scratch.2.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (frame0.tapes 9 (by decide)) array.scratch.2.2.2.2.2.2.2⟩
  have inputs : PowerMachine.BufferNorm.Allocation.inputs⊆allIds := by decide
  have headers1 : WordCleanup.Bounded PowerMachine.BufferNorm.Allocation.clearHeaders H w.val := by
    intro k hk
    obtain ⟨xs,hlen,word⟩:=headers k hk
    have outside : k∉workChanged := by
      simp only [PowerMachine.BufferNorm.Allocation.clearHeaders,List.mem_cons,List.not_mem_nil,or_false] at hk
      simp only [workChanged,workIds,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
      omega
    exact ⟨xs,hlen,BankArray.word_of_eq (frame0.tapes k outside) word⟩
  have positive : 0<planned n 571 := by rw [(plan_outputs n).2.1];exact capacity_pos n
  obtain ⟨c2,t,e2,h2,out,_,temp,f2⟩ := PowerMachine.BufferNorm.Allocation.executes (planned n)
    (planWidth B) H positive (fun k hk=>planned_width n B width k (inputs hk)) input tape w
    (fun k hk=>bank1 k (inputs hk)) scratch
    (RationalAccumulator.blank_of_eq (frame0.tapes 7 (by decide)) array.seven)
    (RationalAccumulator.blank_of_eq (frame0.tapes 37 (by decide)) h37)
    (RationalAccumulator.blank_of_eq (frame0.tapes 216 (by decide)) h216) headers1
  have output : (table n s.val.memory).OutputReady t := by
    have transfer (m pad base : ℕ) (hp : 0<pad) (hm:m=n 788)
        (hwidth:pad=capacity n) (hheap:base=heap n)
        (h:(Profile.Runtime.memoryTable m pad base hp w.val.memory).OutputReady t) :
        (table n s.val.memory).OutputReady t := by
      subst m;subst pad;subst base
      simpa only [table,frame0.memory] using h
    exact transfer _ _ _ positive (plan_outputs n).1 (plan_outputs n).2.1 (plan_outputs n).2.2.1 out
  have frame : BinaryPrecision.Frame changed s.val t.val :=
    (frame0.mono Finset.subset_union_left).trans (f2.mono Finset.subset_union_right)
  have ready : a.Ready t := array.transfer frame.memory (by
    intro k hk
    apply frame.tapes k
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl <;> decide) output.scratch output.seven
  have rawT : Ready slots v t := by
    refine ⟨?_,?_⟩
    · intro k hk
      apply RationalAccumulator.word_of_eq (frame.tapes k _) (raw.1 k hk)
      exact fun hc=>Finset.disjoint_left.mp (by decide : Disjoint (RationalDataflow.ids slots) changed) hk hc
    · intro k hk
      interval_cases k
      · exact output.scratch.1
      · exact output.scratch.2.1
      · exact output.scratch.2.2.1
      · exact output.scratch.2.2.2.1
  have bankT : NatAssign.Bank sourceIds n t.val := by
    intro k hk
    have outside : k∉changed := fun hc=>Finset.disjoint_left.mp
      (by decide : Disjoint sourceIds changed) hk hc
    exact RationalAccumulator.word_of_eq (frame.tapes k outside) (bank k (Finset.mem_union_left _ hk))
  have retained (k : ℕ) (hk:k∈({201,574,787,802}:Finset ℕ)) :
      RationalAccumulator.Word t.val k (planned n k) := by
    have member : k∈workIds := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hk
      simp only [workIds,Finset.mem_insert,Finset.mem_singleton]
      omega
    have outside : k∉PowerMachine.BufferNorm.Allocation.changed := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hk
      simp only [PowerMachine.BufferNorm.Allocation.changed,Finset.mem_insert,Finset.mem_singleton]
      omega
    exact RationalAccumulator.word_of_eq (f2.tapes k outside) (bank1 k (Finset.mem_union_right _ member))
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,ready,rawT,output,bankT,
    by simpa only [(plan_outputs n).2.2.2.2.1] using retained 802 (by decide),
    by simpa only [(plan_outputs n).2.2.2.2.2.1] using retained 201 (by decide),
    by simpa only [(plan_outputs n).2.2.2.2.2.2] using retained 787 (by decide),
    by simpa only [plan_heapEnd n] using retained 574 (by decide),temp,frame⟩
  rw [(plan_outputs n).2.1] at h2
  unfold costBound
  omega

#print axioms executes
end Maxwell.Continuum.RationalDataflow.PartArray.Normalize.Allocation
