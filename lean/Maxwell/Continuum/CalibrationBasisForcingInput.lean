import Maxwell.Continuum.CalibrationBasisForcingAllocated
import Maxwell.Continuum.CalibrationBasisForcingSource
import Maxwell.Continuum.RationalDataflowArrayPromote

/-! Generate and install the basis source as the actual input array. The old
input header words are cleared by executed code; their former interpretation
and all initial memory contents are unrestricted. -/
namespace Maxwell.Continuum.Calibration.BasisForcing
open Maxwell.Cost Maxwell.Cost.Structured FreeFiber RationalDataflow PartArray ArrayDecodeMachine
set_option maxHeartbeats 6000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 2048
attribute [local irreducible] bank allocatedCode sourceTable

def inputCode (column : Fin 24) : Code := .seq (allocatedCode column) Promote.code
def inputCost (R B H I X : ℕ) : ℕ := allocatedCost R B H X+256*(metadataWidth B+I+1)

theorem natural_promote_external (k : ℕ) (hk : k∈naturalIds) : k∉Promote.changed := by
  intro hm
  simp only [Promote.changed,Promote.headers,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl|rfl|rfl|rfl|rfl
  all_goals exact natural_outside _ (by decide) (by decide) (by decide) (by decide) hk

theorem input_executes (column : Fin 24) (n : ℕ → ℕ) (v : ℕ → Parts)
    (agree : ∀k∈ids bank,n k=dataValues v k) (good : Good bank v)
    (B H I : ℕ) (hB : 103≤B) (hR : 2≤n 311)
    (hw : ∀k∈allocationIds,(n k).bits.length≤B) (hv : ∀k∈retained,(v k).Width B)
    (input : List Bool) (tape : ℕ → Bool) (xs : List Bool) (s : Store)
    (hs : NatAssign.Bank allocationIds n s.val) (hz : BankArray.Scratch s.val)
    (h4 : RationalAccumulator.Blank s.val 4) (h7 : RationalAccumulator.Blank s.val 7)
    (h37 : RationalAccumulator.Blank s.val 37) (h216 : RationalAccumulator.Blank s.val 216)
    (headers : WordCleanup.Bounded PowerMachine.BufferNorm.Allocation.clearHeaders H s.val)
    (old : WordCleanup.Bounded Promote.headers I s.val) (hword : BankArray.Word s.val 201 xs) :
    ∃cost t b vf nf finalWord,Executes input tape (inputCode column) cost s t ∧
      cost≤ inputCost (n 311) B H I xs.length ∧ b.Ready t ∧ b.OutputReady t ∧
      sameMetadata (sourceTable (n 311) (n 376) s.val.memory) b ∧
      b.MetadataWidth (metadataWidth B) ∧ Good bank vf ∧
      NatAssign.Bank naturalIds nf t.val ∧ (∀k∈ids bank,nf k=dataValues vf k) ∧
      (∀k∈naturalIds,(nf k).bits.length≤prepareWidth (allocationWidth B)) ∧
      (∀k∈retained,vf k=v k) ∧ nf 311=n 311 ∧
      (∀k,k<5 → RationalAccumulator.Blank t.val k) ∧
      (∀i : Fin (aliasArraySize (n 311)),(b.get i).Valid) ∧
      tableSource (n 311) b=rationalRightCoupling (rationalBasisField column) ∧
      BankArray.Word t.val 201 finalWord ∧ finalWord.length≤allocationWidth B ∧
      t.val.inputHead=s.val.inputHead ∧ t.val.randomCursor=s.val.randomCursor ∧ t.val.output=s.val.output ∧
      RationalAccumulator.Blank t.val 216 ∧
      (∀k∈inversePorts,k≠216 → t.val.tapes k=s.val.tapes k) ∧
      NatAssign.Bank PowerMachine.BufferNorm.Allocation.inputs
        (PowerMachine.BufferNorm.Allocation.outputValues (allocationValues n)) t.val ∧
      RationalAccumulator.Word t.val 376 (n 376) := by
  obtain ⟨c0,u,b,vf,nf,finalWord,e0,hc0,out,metadata,g,natural,agrees,widths,keep,radius,zero,
      values,word,len,ih,random,emitted,temp,continuation,work,heap⟩ :=
    allocated_executes column n v agree good B H hB hw hv input tape xs s hs hz h4 h7 h37 h216 headers hword
  have metaB : b.MetadataWidth (metadataWidth B) :=
    sameMetadata_width _ b metadata _ (sourceTable_metadata n B hB hw s.val.memory)
  have old0 : WordCleanup.Bounded Promote.headers I u.val := by
    intro k hk
    obtain ⟨ys,hy,word⟩ := old k hk
    have member : k∈sourceContinuationPorts ∧ k≠216 := by
      simp only [Promote.headers,List.mem_cons,List.not_mem_nil,or_false] at hk
      simp only [sourceContinuationPorts,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
      constructor
      · exact Or.inr hk
      · omega
    exact ⟨ys,hy,BankArray.word_of_eq (continuation k member.1 member.2) word⟩
  obtain ⟨c1,t,e1,hc1,ready,out1,frame⟩ := Promote.executes b (metadataWidth B) I metaB input tape u out old0
  refine ⟨c0+c1,t,b,vf,nf,finalWord,e0.seq e1,Nat.add_le_add hc0 hc1,ready,out1,metadata,metaB,g,
    (fun k hk => RationalAccumulator.word_of_eq (frame.tapes k (natural_promote_external k hk)) (natural k hk)),
    agrees,widths,keep,radius,?_,(fun i => (values i).1),tableSource_eq column (n 311) hR b (fun i => (values i).2),
    BankArray.word_of_eq (frame.tapes 201 (by decide)) word,len,
    frame.inputHead.trans ih,frame.randomCursor.trans random,frame.output.trans emitted,
    RationalAccumulator.blank_of_eq (frame.tapes 216 (by decide)) temp,?_,?_,?_⟩
  · intro k hk
    apply RationalAccumulator.blank_of_eq (frame.tapes k _) (zero k hk)
    simp only [Promote.changed,Promote.headers,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
    omega
  · intro k hk h216
    have external : k∉Promote.changed := by
      simp only [inversePorts,continuationPorts,Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hk
      simp only [Promote.changed,Promote.headers,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
      omega
    exact (frame.tapes k external).trans (continuation k (Finset.mem_union_left _ hk) h216)
  · intro k hk
    apply RationalAccumulator.word_of_eq (frame.tapes k _) (work k hk)
    simp only [PowerMachine.BufferNorm.Allocation.inputs,Finset.mem_insert,Finset.mem_singleton] at hk
    simp only [Promote.changed,Promote.headers,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
    omega
  · exact RationalAccumulator.word_of_eq (frame.tapes 376 (by decide)) heap

#print axioms input_executes
end Maxwell.Continuum.Calibration.BasisForcing
