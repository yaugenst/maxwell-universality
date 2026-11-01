import Maxwell.Continuum.CalibrationBasisForcingAllocationPlan

/-! Execute the source allocation over arbitrary memory. The width625 is
justified by the raw accumulator proof; the count and addresses are computed. -/
namespace Maxwell.Continuum.Calibration.BasisForcing
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow PartArray ArrayDecodeMachine
set_option maxHeartbeats 6000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 2048
attribute [local irreducible] bank allocationValues

abbrev Allocator := PowerMachine.BufferNorm.Allocation.code
def allocationCode : Code := .seq (NatAssign.code allocationPlan) Allocator
def allocationCost (B H : ℕ) : ℕ := stageCost B+2^60*(allocationWidth B+H+625+3)^2
def sourceTable (R heap : ℕ) (memory : ℕ → Bool) : Table (aliasArraySize R) :=
  Profile.Runtime.memoryTable (aliasArraySize R) 625 heap (by decide) memory

theorem allocation_executes (n : ℕ → ℕ) (v : ℕ → Parts)
    (agree : ∀k∈ids bank,n k=dataValues v k) (B H : ℕ) (hB : 103≤B)
    (hw : ∀k∈allocationIds,(n k).bits.length≤B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : NatAssign.Bank allocationIds n s.val) (hz : BankArray.Scratch s.val)
    (h4 : RationalAccumulator.Blank s.val 4) (h7 : RationalAccumulator.Blank s.val 7)
    (h37 : RationalAccumulator.Blank s.val 37) (h216 : RationalAccumulator.Blank s.val 216)
    (headers : WordCleanup.Bounded PowerMachine.BufferNorm.Allocation.clearHeaders H s.val) :
    ∃cost t,Executes input tape allocationCode cost s t ∧ cost≤allocationCost B H ∧
      (sourceTable (n 311) (n 376) s.val.memory).OutputReady t ∧
      NatAssign.Bank naturalIds (allocationValues n) t.val ∧ Ready bank v t ∧
      (∀k,k<5 → RationalAccumulator.Blank t.val k) ∧ RationalAccumulator.Blank t.val 216 ∧
      t.val.tapes 201=s.val.tapes 201 ∧
      t.val.inputHead=s.val.inputHead ∧ t.val.randomCursor=s.val.randomCursor ∧ t.val.output=s.val.output ∧
      (∀k∈sourceContinuationPorts,k≠216 → t.val.tapes k=s.val.tapes k) ∧
      NatAssign.Bank PowerMachine.BufferNorm.Allocation.inputs
        (PowerMachine.BufferNorm.Allocation.outputValues (allocationValues n)) t.val ∧
      RationalAccumulator.Word t.val 376 (n 376) := by
  have partsSubset : ids bank⊆allocationIds := fun _ hk => Finset.mem_union_left _ (naturalIds_parts hk)
  obtain ⟨c0,u,e0,hc0,b0,r0,z0,f0⟩ := naturalStage_parts bank allocationIds partsSubset allocationIds_ge
    allocationPlan allocation_valid (by decide) n v B hw (allocation_literals B hB)
    (by simpa only [allocationValues] using allocation_agrees n v agree) input tape s hs (by
      intro k hk
      interval_cases k
      · exact hz.1
      · exact hz.2.1
      · exact hz.2.2.1
      · exact hz.2.2.2.1) h4
  have bank0 : NatAssign.Bank allocationIds (allocationValues n) u.val := by
    simpa only [allocationValues] using b0
  have scratch : BankArray.Scratch u.val :=
    ⟨z0 0 (by decide),z0 1 (by decide),z0 2 (by decide),z0 3 (by decide),
      RationalAccumulator.blank_of_eq (f0.tapes 5 (allocation_stage_external 5 (by simp))) hz.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (f0.tapes 6 (allocation_stage_external 6 (by simp))) hz.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (f0.tapes 8 (allocation_stage_external 8 (by simp))) hz.2.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (f0.tapes 9 (allocation_stage_external 9 (by simp))) hz.2.2.2.2.2.2.2⟩
  have headers0 : WordCleanup.Bounded PowerMachine.BufferNorm.Allocation.clearHeaders H u.val := by
    intro k hk
    obtain ⟨xs,hlen,word⟩ := headers k hk
    refine ⟨xs,hlen,BankArray.word_of_eq (f0.tapes k (allocation_stage_external k ?_)) word⟩
    simp only [PowerMachine.BufferNorm.Allocation.clearHeaders,List.mem_cons,List.not_mem_nil,or_false] at hk ⊢
    tauto
  have inputSubset : PowerMachine.BufferNorm.Allocation.inputs⊆allocationIds := by
    intro k hk
    apply Finset.mem_union_right
    simp only [PowerMachine.BufferNorm.Allocation.inputs,Finset.mem_insert,Finset.mem_singleton] at hk ⊢
    tauto
  have outputs := allocation_outputs n
  have positive : 0<allocationValues n 571 := by rw [outputs.2.2.1];decide
  obtain ⟨c1,t,e1,hc1,table,allocatorBank,temp,f1⟩ := PowerMachine.BufferNorm.Allocation.executes
    (allocationValues n) (allocationWidth B) H positive
    (fun k hk => allocation_width n B hB hw k (inputSubset hk)) input tape u
    (fun k hk => bank0 k (inputSubset hk)) scratch
    (RationalAccumulator.blank_of_eq (f0.tapes 7 (allocation_stage_external 7 (by simp))) h7)
    (RationalAccumulator.blank_of_eq (f0.tapes 37 (allocation_stage_external 37 (by simp))) h37)
    (RationalAccumulator.blank_of_eq (f0.tapes 216 (allocation_stage_external 216 (by simp))) h216) headers0
  have table' : (sourceTable (n 311) (n 376) s.val.memory).OutputReady t := by
    have transfer (m w heap : ℕ) (hp : 0<w) (hm : m=aliasArraySize (n 311))
        (hwidth : w=625) (hheap : heap=n 376)
        (h : (Profile.Runtime.memoryTable m w heap hp u.val.memory).OutputReady t) :
        (sourceTable (n 311) (n 376) s.val.memory).OutputReady t := by
      subst m
      subst w
      subst heap
      simpa only [sourceTable,f0.memory] using h
    exact transfer _ _ _ positive outputs.2.1 outputs.2.2.1 outputs.2.2.2.1 table
  have natural : NatAssign.Bank naturalIds (allocationValues n) t.val := fun k hk =>
    RationalAccumulator.word_of_eq (f1.tapes k (allocation_preserves_natural k hk))
      (bank0 k (Finset.mem_union_left _ hk))
  have blank (k : ℕ) (hk : k<5) : RationalAccumulator.Blank t.val k := by
    by_cases he : k<4
    · interval_cases k
      · exact table'.scratch.1
      · exact table'.scratch.2.1
      · exact table'.scratch.2.2.1
      · exact table'.scratch.2.2.2.1
    · have eq : k=4 := by omega
      subst k
      exact RationalAccumulator.blank_of_eq (f1.tapes 4 (by decide)) (z0 4 (by decide))
  have ready : Ready bank v t := ⟨fun k hk => by
    have hh := natural k (naturalIds_parts hk)
    simpa only [allocation_agrees n v agree k hk] using hh,fun k hk => blank k (by omega)⟩
  refine ⟨c0+c1,t,e0.seq e1,?_,table',natural,ready,blank,temp,
    (f1.tapes 201 (by decide)).trans (f0.tapes 201 (allocation_stage_external 201 (by simp))),
    f1.inputHead.trans f0.inputHead,f1.randomCursor.trans f0.randomCursor,f1.output.trans f0.output,?_,?_,?_⟩
  · rw [outputs.2.2.1] at hc1
    exact Nat.add_le_add hc0 hc1
  · intro k hk h216
    have hh := continuation_outside k (Finset.mem_union_left _ hk)
    have unchanged : k∉({0,1,2,3,4}∪allocationIds:Finset ℕ) := by
      have notExtra : k∉({376,570,571,572,573}:Finset ℕ) := by
        simp only [sourceContinuationPorts,inversePorts,continuationPorts,Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hk
        simp only [Finset.mem_insert,Finset.mem_singleton]
        omega
      intro hm
      simp only [allocationIds,Finset.mem_union] at hm
      rcases hm with hz|hn|he
      · exact hh.2.1 (Finset.mem_union_left _ hz)
      · exact hh.2.1 (Finset.mem_union_right _ hn)
      · exact notExtra he
    have outside : k∉PowerMachine.BufferNorm.Allocation.changed := by
      simp only [sourceContinuationPorts,inversePorts,continuationPorts,Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hk
      simp only [PowerMachine.BufferNorm.Allocation.changed,Finset.mem_insert,Finset.mem_singleton]
      omega
    exact (f1.tapes k outside).trans (f0.tapes k unchanged)
  · exact fun k hk=>allocatorBank k (Finset.mem_union_left _ hk)
  · have heap:=bank0 376 (Finset.mem_union_right _ (by simp))
    rw [allocationValues_keep n 376 (by decide)] at heap
    exact RationalAccumulator.word_of_eq (f1.tapes 376 (by decide)) heap

theorem sourceTable_metadata (n : ℕ → ℕ) (B : ℕ) (hB : 103≤B)
    (hw : ∀k∈allocationIds,(n k).bits.length≤B) (memory : ℕ → Bool) :
    (sourceTable (n 311) (n 376) memory).MetadataWidth (metadataWidth B) := by
  have bits : (aliasArraySize (n 311)).bits.length≤allocationWidth B := by
    have h := allocation_width n B hB hw 570 (Finset.mem_union_right _ (by simp))
    rwa [(allocation_outputs n).2.1] at h
  have heap := hw 376 (Finset.mem_union_right _ (by simp))
  have base : B≤allocationWidth B := by unfold allocationWidth;omega
  apply Profile.Runtime.memoryTable_metadata
  · unfold metadataWidth;omega
  · rw [show (625:ℕ).bits.length=10 by decide]
    unfold metadataWidth
    omega

#print axioms allocation_executes
end Maxwell.Continuum.Calibration.BasisForcing
