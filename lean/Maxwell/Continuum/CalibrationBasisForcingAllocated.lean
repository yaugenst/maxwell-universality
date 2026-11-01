import Maxwell.Continuum.CalibrationBasisForcingAllocation

/-! Actual basis-source generation from runtime radius, scalar words, and free
heap pointer. Destination metadata, width clock, count, and coefficients are
all produced by the program; initial memory contents are unrestricted. -/
namespace Maxwell.Continuum.Calibration.BasisForcing
open Maxwell.Cost Maxwell.Cost.Structured FreeFiber RationalDataflow PartArray ArrayDecodeMachine
set_option maxHeartbeats 6000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 2048
attribute [local irreducible] bank allocationCode tableCode sourceTable

def allocatedCode (column : Fin 24) : Code :=
  .seq allocationCode (.seq (WordReplace.code 315 201) (tableCode column))
def allocatedCost (R B H X : ℕ) : ℕ := allocationCost B H+6*X+15*allocationWidth B+21+
  (aliasArraySize R+1)*(13*allocationWidth B+15)+
  aliasArraySize R*bodyCost (allocationWidth B) (metadataWidth B)

theorem allocated_executes (column : Fin 24) (n : ℕ → ℕ) (v : ℕ → Parts)
    (agree : ∀k∈ids bank,n k=dataValues v k) (good : Good bank v)
    (B H : ℕ) (hB : 103≤B) (hw : ∀k∈allocationIds,(n k).bits.length≤B)
    (hv : ∀k∈retained,(v k).Width B)
    (input : List Bool) (tape : ℕ → Bool) (xs : List Bool) (s : Store)
    (hs : NatAssign.Bank allocationIds n s.val) (hz : BankArray.Scratch s.val)
    (h4 : RationalAccumulator.Blank s.val 4) (h7 : RationalAccumulator.Blank s.val 7)
    (h37 : RationalAccumulator.Blank s.val 37) (h216 : RationalAccumulator.Blank s.val 216)
    (headers : WordCleanup.Bounded PowerMachine.BufferNorm.Allocation.clearHeaders H s.val)
    (hword : BankArray.Word s.val 201 xs) :
    ∃cost t b vf nf finalWord,Executes input tape (allocatedCode column) cost s t ∧
      cost≤allocatedCost (n 311) B H xs.length ∧ b.OutputReady t ∧
      sameMetadata (sourceTable (n 311) (n 376) s.val.memory) b ∧ Good bank vf ∧
      NatAssign.Bank naturalIds nf t.val ∧ (∀k∈ids bank,nf k=dataValues vf k) ∧
      (∀k∈naturalIds,(nf k).bits.length≤prepareWidth (allocationWidth B)) ∧
      (∀k∈retained,vf k=v k) ∧ nf 311=n 311 ∧
      (∀k,k<5 → RationalAccumulator.Blank t.val k) ∧
      (∀i : Fin (aliasArraySize (n 311)),(b.get i).Valid ∧
        (b.get i).value=rationalRightCoupling (rationalBasisField column)
          (arrayAliasAt (n 311) i) (arrayPolarizationAt (n 311) i)) ∧
      BankArray.Word t.val 201 finalWord ∧ finalWord.length≤allocationWidth B ∧
      t.val.inputHead=s.val.inputHead ∧ t.val.randomCursor=s.val.randomCursor ∧ t.val.output=s.val.output ∧ RationalAccumulator.Blank t.val 216 ∧
      (∀k∈sourceContinuationPorts,k≠216 → t.val.tapes k=s.val.tapes k) ∧
      NatAssign.Bank PowerMachine.BufferNorm.Allocation.inputs
        (PowerMachine.BufferNorm.Allocation.outputValues (allocationValues n)) t.val ∧
      RationalAccumulator.Word t.val 376 (n 376) := by
  obtain ⟨c0,u,e0,hc0,table0,n0,r0,z0,temp0,counter0,ih0,random0,emitted0,continuation0,work0,heap0⟩ :=
    allocation_executes n v agree B H hB hw input tape s hs hz h4 h7 h37 h216 headers
  have word315 := n0 315 (naturalIds_decode (by decide))
  rw [(allocation_outputs n).1] at word315
  obtain ⟨u1,e1,word1,f1⟩ := WordReplace.executes 315 201 (by decide) input tape
    (aliasArraySize (n 311)).bits xs u word315 (BankArray.word_of_eq counter0 hword)
  have natural : NatAssign.Bank naturalIds (allocationValues n) u1.val := fun k hk =>
    RationalAccumulator.word_of_eq (f1.2.2.2.2.2.1 k (fun he => naturalIds_counter (he ▸ hk))) (n0 k hk)
  have blank (k : ℕ) (hk : k<5) : RationalAccumulator.Blank u1.val k :=
    RationalAccumulator.blank_of_eq (f1.2.2.2.2.2.1 k (by omega)) (z0 k hk)
  have scratch : BankArray.Scratch u1.val := by
    rcases table0.scratch with ⟨h0,h1,h2,h3,h5,h6,h8,h9⟩
    exact ⟨blank 0 (by decide),blank 1 (by decide),blank 2 (by decide),blank 3 (by decide),
      RationalAccumulator.blank_of_eq (f1.2.2.2.2.2.1 5 (by decide)) h5,
      RationalAccumulator.blank_of_eq (f1.2.2.2.2.2.1 6 (by decide)) h6,
      RationalAccumulator.blank_of_eq (f1.2.2.2.2.2.1 8 (by decide)) h8,
      RationalAccumulator.blank_of_eq (f1.2.2.2.2.2.1 9 (by decide)) h9⟩
  have table1 := table0.copy_frame (Or.inl rfl) f1 scratch
    (RationalAccumulator.blank_of_eq (f1.2.2.2.2.2.1 7 (by decide)) table0.seven)
  have widths := allocation_width n B hB hw
  have hBC : B≤allocationWidth B := by unfold allocationWidth;omega
  have hCP : allocationWidth B≤prepareWidth (allocationWidth B) := by unfold prepareWidth;omega
  have hcount : (aliasArraySize (n 311)).bits.length≤allocationWidth B := by
    have h := widths 315 (Finset.mem_union_left _ (naturalIds_decode (by decide)))
    rwa [(allocation_outputs n).1] at h
  have radius := allocationValues_keep n 311 (by decide)
  obtain ⟨origin,word1⟩ := word1
  obtain ⟨c2,t,b,vf,nf,finalWord,e2,hc2,table2,metadata,g2,n2,agree2,w2,keep,radius2,z2,values,word2,len2,ih2,random2,emitted2,continuation⟩ :=
    table_executes column (n 311) (allocationWidth B) (metadataWidth B) (hB.trans hBC)
      (sourceTable (n 311) (n 376) s.val.memory) v (allocationValues n)
      (allocation_agrees n v agree) good
      (fun k hk => (widths k (Finset.mem_union_left _ hk)).trans hCP)
      (fun k hk => (hv k hk).mono hBC)
      ((hw 311 (Finset.mem_union_left _ (naturalIds_decode (by decide)))).trans hBC) radius
      (sourceTable_metadata n B hB hw s.val.memory)
      (by unfold sourceTable Profile.Runtime.memoryTable;rw [addressValue_bits])
      (by unfold sourceTable;exact Profile.Runtime.memoryTable_separated _ _ _ (by decide) _)
      input tape (aliasArraySize (n 311)).bits origin hcount (addressValue_bits _) u1 natural blank table1 word1
  refine ⟨c0+((6*xs.length+15*(aliasArraySize (n 311)).bits.length+21)+c2),t,b,vf,nf,finalWord,
    e0.seq (e1.seq e2),?_,table2,metadata,g2,n2,agree2,w2,keep,radius2,z2,values,⟨origin,word2⟩,
    len2.trans_le hcount,ih2.trans (f1.2.1.trans ih0),random2.trans (f1.2.2.2.1.trans random0),
    emitted2.trans (f1.2.2.2.2.1.trans emitted0),?_,?_,?_,?_⟩
  · have countCost := Nat.mul_le_mul_left (aliasArraySize (n 311)+1)
      (show 13*(aliasArraySize (n 311)).bits.length+15≤13*allocationWidth B+15 by omega)
    unfold allocatedCost
    omega
  · exact RationalAccumulator.blank_of_eq ((continuation 216 (by decide)).trans
      (f1.2.2.2.2.2.1 216 (by decide))) temp0
  · intro k hk h216
    exact (continuation k (Finset.mem_union_left _ hk)).trans ((f1.2.2.2.2.2.1 k (continuation_outside k (Finset.mem_union_left _ hk)).2.2.2).trans
      (continuation0 k hk h216))
  · intro k hk
    have member:k∈sourceLoopPorts:=Finset.mem_union_right _ (Finset.mem_insert_of_mem hk)
    exact RationalAccumulator.word_of_eq ((continuation k member).trans
      (f1.2.2.2.2.2.1 k (continuation_outside k member).2.2.2)) (work0 k hk)
  · exact RationalAccumulator.word_of_eq ((continuation 376 (by decide)).trans
      (f1.2.2.2.2.2.1 376 (by decide))) heap0

#print axioms allocated_executes
end Maxwell.Continuum.Calibration.BasisForcing
