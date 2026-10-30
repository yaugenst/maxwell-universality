import Maxwell.Continuum.ProfileEndpointFrame
import Maxwell.Continuum.ProfileCorrectionInitialization
import Maxwell.Continuum.RationalDataflowWordReplace

/-! The complete fixed endpoint-correction stage: compute both moments,
reload the runtime index, initialize the dyadic scale, and fill the final
encoded profile table. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def finalizeCode : Code := .seq (WordReplace.code 661 201)
  (.seq endpointProgram (.seq (WordReplace.code 661 201)
    (.seq correctionInitializeCode correctionMapCode)))
def finalizeValues {n : ℕ} (a : PartArray.Table n) (P : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  correctionInitialValues n P (endpointValues a (dftResetValues v) n)
def finalizeTable {n : ℕ} (a b : PartArray.Table n) (P : ℕ) (v : ℕ→Parts) : PartArray.Table n :=
  correctionMapTable a b (finalizeValues a P v)
def finalizeOutputValues {n : ℕ} (a : PartArray.Table n) (P : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  correctionValues a (finalizeValues a P v) n
def finalizeCost (n P W oldLength : ℕ) : ℕ :=
  6*oldLength+15*n.bits.length+21+endpointCost n W n.bits.length+
    (21*n.bits.length+21)+
    (3*operationCost (endpointWorkingWidth n W)+31*n.bits.length+31*((2:ℕ)^P).bits.length+85)+
    correctionMapCost n (endpointWorkingWidth n W) n.bits.length

theorem finalize_executes (N W : ℕ) (hW : 1≤W)
    (a b : PartArray.Table (profileDegree N))
    (ha : ∀i,(a.get i).Width W) (hd : ∀i,(a.get i).denominator=1)
    (he : ∀i,(a.get i).value=((roundedCoefficient N i.val).numerator:ℚ))
    (ham : a.MetadataWidth W)
    (hbm : b.MetadataWidth (correctionWorkingWidth (profileDegree N) (endpointWorkingWidth (profileDegree N) W)))
    (hslot : correctionWorkingWidth (profileDegree N) (endpointWorkingWidth (profileDegree N) W)≤addressValue b.width)
    (hsep : b.Separated) (hdis : a.SeparatedFrom b)
    (hn : (profileDegree N).bits.length≤W) (hpw : ((2:ℕ)^profileWorkBits N).bits.length≤W)
    (v : ℕ→Parts) (hw : WidthBank dftRegisters W v)
    (input : List Bool) (tape : ℕ→Bool) (oldWord : List Bool) (s : Store)
    (hs : SharedConversion.Ready dftRegisters v s) (hat : a.Ready s) (hbt : b.OutputReady s)
    (hcount : BankArray.Word s.val 201 oldWord)
    (hsize : Word s.val 661 (profileDegree N)) (hpower : Word s.val 144 (2^profileWorkBits N)) :
    ∃cost t finalWord,Executes input tape finalizeCode cost s t ∧
      cost≤finalizeCost (profileDegree N) (profileWorkBits N) W oldWord.length ∧
      SharedConversion.Ready dftRegisters (finalizeOutputValues a (profileWorkBits N) v) t ∧
      Good dftRegisters (finalizeOutputValues a (profileWorkBits N) v) ∧
      WidthBank dftRegisters
        (correctionWorkingWidth (profileDegree N) (endpointWorkingWidth (profileDegree N) W))
        (finalizeOutputValues a (profileWorkBits N) v) ∧
      (finalizeTable a b (profileWorkBits N) v).OutputReady t ∧ a.Ready t ∧
      BankArray.Word t.val 201 finalWord ∧ finalWord.length=(profileDegree N).bits.length ∧
      (∀i:Fin (profileDegree N),((finalizeTable a b (profileWorkBits N) v).get i).Valid ∧
        ((finalizeTable a b (profileWorkBits N) v).get i).Width
          (correctionWorkingWidth (profileDegree N) (endpointWorkingWidth (profileDegree N) W)) ∧
        ((finalizeTable a b (profileWorkBits N) v).get i).value=(encodedCoefficient N i.val).value) ∧
      Word t.val 661 (profileDegree N) ∧ Word t.val 144 (2^profileWorkBits N) := by
  let n := profileDegree N
  let P := profileWorkBits N
  let B := endpointWorkingWidth n W
  let M := correctionWorkingWidth n B
  have hWB : W≤B := by dsimp [B,endpointWorkingWidth];omega
  have hBM : B≤M := by dsimp [M,correctionWorkingWidth];omega
  have hWM := hWB.trans hBM
  have hB : 1≤B := hW.trans hWB
  have hav (i : Fin n) : (a.get i).Valid := by simp only [Parts.Valid,hd i];exact Nat.zero_lt_one
  obtain ⟨s0,e0,count0,f0⟩ := WordReplace.executes 661 201 (by decide) input tape n.bits oldWord s hsize hcount
  have state0 := PartArray.sharedReady_copy_frame hs (Or.inl rfl) f0
  have at0 := hat.copy_frame (Or.inl rfl) f0
  have bt0 := hbt.copy_frame (Or.inl rfl) f0 at0.scratch at0.seven
  obtain ⟨origin0,count0⟩ := count0
  obtain ⟨c1,s1,word1,e1,r1,at1,count1,len1,hc1,hg1,hw1,_,_⟩ := endpoint_executes a W hW ham ha hd v hw
    input tape n.bits origin0 hn s0 (addressValue_bits n) count0 state0.rational at0
  let v1 := endpointValues a (dftResetValues v) n
  change Ready dftRegisters v1 s1 at r1
  change IntegerBank dftRegisters v1 at hg1
  change WidthBank dftRegisters B v1 at hw1
  have state1 := endpoint_shared_ready e1 state0 r1
  have bt1 := endpoint_output_ready e1 bt0 at1
  have size1 : Word s1.val 661 n := word_of_eq
    ((endpoint_keep e1 661 (by simp [endpointProtected])).trans (f0.2.2.2.2.2.1 661 (by decide))) hsize
  have power1 : Word s1.val 144 (2^P) := word_of_eq
    ((endpoint_keep e1 144 (by simp [endpointProtected])).trans (f0.2.2.2.2.2.1 144 (by decide))) hpower
  obtain ⟨s2,e2,count2,f2⟩ := WordReplace.executes 661 201 (by decide) input tape n.bits word1 s1 size1 ⟨origin0,count1⟩
  have state2 := PartArray.sharedReady_copy_frame state1 (Or.inl rfl) f2
  have at2 := at1.copy_frame (Or.inl rfl) f2
  have bt2 := bt1.copy_frame (Or.inl rfl) f2 at2.scratch at2.seven
  have power2 := word_of_eq (f2.2.2.2.2.2.1 144 (by decide)) power1
  obtain ⟨c3,s3,e3,hc3,r3,f3⟩ := correction_initialize_executes n P B v1 hB hw1 n.bits (addressValue_bits n)
    input tape s2 state2.rational count2 power2
  let v3 := correctionInitialValues n P v1
  change Ready dftRegisters v3 s3 at r3
  have state3 := PartArray.sharedReady_arithmetic_frame state2 f3 r3
  have at3 := at2.arithmetic_frame _ f3 r3.2
  have bt3 := bt2.shared_frame _ (f3.mono (PartArray.workspace_subset_shared _)) at3.scratch at3.seven
  have hw3 : WidthBank dftRegisters B v3 := correctionInitialValues_width n P B v1 hB
    (hn.trans hWB) (hpw.trans hWB) hw1
  have hg3 : Good dftRegisters v3 := correctionInitialValues_good n P v1 hg1.good
  have constants := correctionInitialValues_constants n P v1
  have hconst (i : ℕ) (hi : i∈correctionConstants) : (v3 i).Width B := by
    apply hw3 i
    simp only [correctionConstants,Finset.mem_insert,Finset.mem_singleton] at hi
    simp only [dftRegisters,Finset.mem_range]
    omega
  obtain ⟨origin2,count2⟩ := count2
  have count3 : s3.val.tapes 201=BitTape.shifted n.bits origin2 :=
    (f3.tapes 201 (outside_workspace _ _ (by decide))).trans count2
  have h8v : (v3 8).value=(n:ℚ) := by
    change (correctionInitialValues n P v1 8).value=(n:ℚ)
    rw [constants.2.2.2.1]
    simp [Parts.value]
  have finalInvariant := correction_invariant a v3 B hB (fun i => (ha i).mono hWB) hav
    hg3 (hw3.mono hBM) hconst constants.2.2.1 (hw3 8 (by decide)) h8v n le_rfl
  obtain ⟨c4,t,word,e4,hc4,state4,at4,bt4,count4,len4,correct⟩ := correction_map_executes a b B hB
    (fun i => (ha i).mono hWB)
    hav v3 hg3 (hw3.mono hBM) hconst constants.2.2.1 (hw3 8 (by decide))
    h8v
    (ham.mono hWM) hbm hslot hsep hdis input tape n.bits origin2
    (hn.trans hWM) s3 (addressValue_bits n) count3 state3 at3 bt3
  have initialGood : Good dftRegisters (dftResetValues v) := by
    intro i hi
    rw [dftResetValues_eq,ite_eq_left (Finset.mem_range.mp hi)]
    exact Parts.literal_valid 0
  have moments := endpointValues_profile N a (dftResetValues v) hav he initialGood (by
    simp [dftResetValues_eq,Parts.literal_value])
  refine ⟨_,t,word,e0.seq (e1.seq (e2.seq (e3.seq e4))),?_,state4,
    finalInvariant.good,finalInvariant.width,bt4,at4,⟨origin2,count4⟩,len4,?_,?_,?_⟩
  · dsimp only [n,P,B] at hc1 hc3 hc4 len1 len4 ⊢
    rw [len1]
    unfold finalizeCost
    omega
  · intro i
    obtain ⟨valid,width,value⟩ := correct i
    refine ⟨valid,width,value.trans ?_⟩
    have ve : (v3 0).value=(endpointInteger N).value := congrArg Parts.value constants.1 |>.trans moments.1
    have vs : (v3 3).value=(slopeInteger N).value := congrArg Parts.value constants.2.1 |>.trans moments.2
    have scale : (v3 6).value=((2:ℚ)^P)⁻¹ := by
      change (correctionInitialValues n P v1 6).value=_
      rw [constants.2.2.2.2]
      simp only [Parts.value,Nat.cast_one,Nat.cast_zero,sub_zero,
        Nat.cast_pow,Nat.cast_ofNat,one_div]
    rw [ve,vs,scale,he i]
    exact correctedValue_profile N i.val
  · exact word_of_eq
      ((e4.protectsTape 661 (by decide)).trans
        ((f3.tapes 661 (outside_workspace _ _ (by decide))).trans
          (f2.2.2.2.2.2.1 661 (by decide)))) size1
  · exact word_of_eq ((e4.protectsTape 144 (by decide)).trans
      (f3.tapes 144 (outside_workspace _ _ (by decide)))) power2

#print axioms finalize_executes
end Maxwell.Continuum.Profile.Runtime
