import Maxwell.Continuum.CalibrationInversePrepare

/-! A single fixed program generates the literal inverse coefficients,
converts their raw denominators, initializes the arrays, and executes the
cached inverse. No coefficient table, inverse snapshot, or execution trace
is supplied to this theorem. -/

namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix RationalDataflow NeumannMachine
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768

def generatedInverseCode : Code := .seq generatedCoefficientCode
  (.seq PartArray.headerSwapCode (.seq inversePrepareCode convertedCode))
def continuationBudget (W B : ℕ) : ℕ := max W (2^14*(B+1))

theorem sameMetadata_layout {n : ℕ} (a b : PartArray.Table (tableSize n)) (heap : ℕ)
    (h : sameMetadata a b) (ha : SourceLayout a heap) : SourceLayout b heap := by
  obtain ⟨hw,hp,hn,hd,_⟩ := h
  constructor
  · simpa only [hw] using ha.canonical
  · exact hp.trans ha.positive
  · simpa only [hw,hn] using ha.negative
  · simpa only [hw,hd] using ha.denominator

theorem continuationBudget_ge (W B : ℕ) : W≤continuationBudget W B ∧ B≤continuationBudget W B := by
  exact ⟨le_max_left _ _,(by omega : B≤2^14*(B+1)).trans (le_max_right _ _)⟩

theorem inverse_tail_protects : ∀ k∈Finset.Icc 530 534,
    inversePrepareCode.protectsTape k=true ∧ convertedCode.protectsTape k=true := by decide

theorem generated_inverse_executes (R : ℕ) (a : PartArray.Table (aliasArraySize R))
    (b : PartArray.Table (tableSize (aliasArraySize R))) (rawHeap B W BN : ℕ) (hB : 101≤B)
    (v : ℕ → Parts) (natural d unused : ℕ → ℕ)
    (hn : ∀ k∈ids RawFree.neighborRegisters, natural k=dataValues v k)
    (hw : ∀ k∈emissionIds, (natural k).bits.length≤B)
    (hp : ∀ k∈matrixParameters, (v k).Width B ∧ (v k).Valid) (hradius : natural 311=R)
    (hdim : d 300=aliasArraySize R)
    (hd : ∀ k∈Finset.Icc 300 309, (d k).bits.length≤BN)
    (hu : ∀ k∈Finset.Icc 107 140, (unused k).bits.length≤BN)
    (haValid : ∀ i, (a.get i).Valid) (haMeta : a.MetadataWidth B) (hbMeta : b.MetadataWidth W)
    (hfit : coefficientWidth (countWidth B)≤addressValue b.width)
    (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b) (hraw : SourceLayout b rawHeap)
    (hheap : rawHeap+3*tableSize (aliasArraySize R)*addressValue b.width≤d 302)
    (hshared : PartArray.sharedWidth (tableSize (aliasArraySize R)) W≤continuationBudget W BN)
    (hprepare : 2^CopyPlan.plan.length*(continuationBudget W BN+1)≤d 301)
    (hslot : commonWidth (aliasArraySize R) (d 304) (W+1)≤d 301)
    (haddress : (d 302).bits.length+2*(aliasArraySize R).bits.length+(d 301).bits.length+10≤d 301)
    (ht : (3:ℝ)≤(v 0).value) (hE : (7:ℝ)≤(v 1).value ∧ ((v 1).value:ℝ)≤8)
    (hr : ∀ k, |((RawFree.quasiParts v k).value:ℝ)|≤1/16)
    (input : List Bool) (tape : ℕ → Bool) (xs : List Bool) (hlen : xs.length≤B) (s : Store)
    (hs : NatAssign.Bank emissionIds natural s.val)
    (hinputs : NatAssign.Bank (Finset.Icc 300 309) d s.val)
    (hunused : NatAssign.Bank (Finset.Icc 107 140) unused s.val)
    (hz : ∀ k, k<5 → RationalAccumulator.Blank s.val k)
    (ha : a.Ready s) (hb : b.OutputReady s) (hword : BankArray.Word s.val 201 xs)
    (h206 : RationalAccumulator.Blank s.val 206) (h216 : RationalAccumulator.Blank s.val 216) :
    ∃ (cost : ℕ) (t : Store) (coeff : CoefficientIndex (aliasArraySize R) → Parts)
        (out : Snapshot (aliasArraySize R)),
      Executes input tape generatedInverseCode cost s t ∧
      cost≤generatedCoefficientCost R B W+256*(B+W+1)+
        inversePrepareCost (coefficientWidth (countWidth B)) BN B (d 301)
          (coefficientBaseWidth (countWidth B)) (tableSize (aliasArraySize R))+
        convertedCost (aliasArraySize R) (d 301) (d 302) (SharedTable.denominator coeff) (d 304)
          W (continuationBudget W BN) (addressValue b.width) (tableSize (aliasArraySize R)).bits.length ∧
      (∀ i, (coeff i).Valid ∧ (coeff i).Width W ∧
        (coeff i).value=cachedCoefficientTable (v 0).value (v 1).value
          (fun j => (RawFree.quasiParts v j).value) R (tableSource R a) i) ∧
      out.Ready (aliasArraySize R).bits
        (initializedWidth (aliasArraySize R) (d 301) (d 302) (SharedTable.denominator coeff)
          (d 304) (d 301)) t.val ∧
      out.data.Sized (initializedWidth (aliasArraySize R) (d 301) (d 302) (SharedTable.denominator coeff)
        (d 304) (d 301)) ∧
      RationalAccumulator.Word t.val 126 (SharedTable.denominator coeff) ∧
      RationalAccumulator.Word t.val 304 (d 304) ∧
      (∀ k∈Finset.Icc 530 534, t.val.tapes k=s.val.tapes k) ∧
      ∀ i : Fin (aliasArraySize R), ((Horner.channels out.words 10 11).value i : ℚ)/
          (SharedTable.denominator coeff : ℚ)^(d 304+1)=
        (cachedInverseApply (v 0).value (v 1).value (fun j => (RawFree.quasiParts v j).value)
          R (tableSource R a) (d 304+1)).get i := by
  let U := coefficientWidth (countWidth B)
  have hBU : B≤U := (countWidth_ge B).trans (coefficientWidth_ge (countWidth B))
  have hUW : U≤W := by
    have hm : addressValue b.width≤W := by rw [←b.clock_length]; exact hbMeta.clock
    exact hfit.trans hm
  have hW : 0<W := by omega
  have hwidth : 0<d 301 := by omega
  have hcounterWidth : (tableSize (aliasArraySize R)).bits.length≤W := by
    have h := countPlans_width paddedCountPlan (Or.inr (Or.inr rfl)) natural B (by omega) hw 332 (by decide)
    rw [paddedCount_value,hradius] at h
    exact h.trans ((coefficientWidth_ge (countWidth B)).trans hUW)
  obtain ⟨c0,u0,c,vf,nf,word0,e0,hc0,out0,meta0,bank0,agree0,width0,parameters,radius,z0,padded,
      values,count0,len0,headers,continuation⟩ := generatedCoefficient_executes R a b B W hB v natural
    hn hw hp hradius haValid haMeta hbMeta hfit hsep hdisjoint ht hE hr input tape xs hlen s hs hz ha hb hword
  have metaC := sameMetadata_width b c meta0 W hbMeta
  have layoutC := sameMetadata_layout b c rawHeap meta0 hraw
  obtain ⟨c1,u1,e1,hc1,source1,old1,ready1,temp1,f1⟩ := generated_header_executes a c B W haMeta
    metaC vf nf agree0 input tape u0 headers out0 bank0 z0 (continuation.blank216 h216)
  have bank1 : NatAssign.Bank emissionIds nf u1.val := by
    intro k hk
    have hout : k∉insert 216 PartArray.headerSlots := fun hh =>
      Finset.disjoint_left.mp (show Disjoint emissionIds (insert 216 PartArray.headerSlots) by decide) hk hh
    exact RationalAccumulator.word_of_eq (f1.tapes k hout) (bank0 k hk)
  have inputs1 : NatAssign.Bank (Finset.Icc 300 309) d u1.val := by
    intro k hk
    have ho : k∉insert 216 PartArray.headerSlots := by
      have h := Finset.mem_Icc.mp hk
      simp only [PartArray.headerSlots,Finset.mem_insert,Finset.mem_singleton]
      omega
    exact RationalAccumulator.word_of_eq (f1.tapes k ho) (continuation.naturalInputs hinputs k hk)
  have unused1 : NatAssign.Bank (Finset.Icc 107 140) unused u1.val := by
    intro k hk
    have ho : k∉insert 216 PartArray.headerSlots := by
      have h := Finset.mem_Icc.mp hk
      simp only [PartArray.headerSlots,Finset.mem_insert,Finset.mem_singleton]
      omega
    exact RationalAccumulator.word_of_eq (f1.tapes k ho) (continuation.descriptorUnused hunused k hk)
  have blank1 : ∀ k, k<5 → RationalAccumulator.Blank u1.val k := by
    intro k hk
    apply RationalAccumulator.blank_of_eq (f1.tapes k _) (z0 k hk)
    simp only [PartArray.headerSlots,Finset.mem_insert,Finset.mem_singleton]
    omega
  have param1 : ∀ k∈matrixParameters, (vf k).Width U ∧ (vf k).Valid := by
    intro k hk
    rw [parameters k hk]
    exact ⟨(hp k hk).1.mono hBU,(hp k hk).2⟩
  have oldMeta : (refreshTable a u0.val.memory).MetadataWidth B :=
    ⟨haMeta.width,haMeta.basePositive,haMeta.baseNegative,haMeta.baseDenominator,haMeta.clock⟩
  have saved1 := RationalAccumulator.blank_of_eq (f1.tapes 206 (by decide)) (continuation.blank206 h206)
  obtain ⟨c2,u2,e2,hc2,source2,target2,shared2,sharedWidth2,desc2,inputs2,bits2,count2,saved2,temp2⟩ :=
    inverse_prepare_executes c (refreshTable a u0.val.memory) rawHeap layoutC vf nf d unused U BN B W
      (by omega) hUW metaC oldMeta agree0 width0 param1 hd hu hwidth input tape word0 u1 bank1
      inputs1 unused1 blank1 source1 old1 (BankArray.word_of_eq (f1.tapes 201 (by decide)) count0) saved1 temp1
  let target := Allocation.table (aliasArraySize R) (d 301) (d 302) hwidth u1.val.memory
  have targetReady : target.OutputReady u2 := by
    exact (congrArg (fun n => (Allocation.table n (d 301) (d 302) hwidth
      u1.val.memory).OutputReady u2) hdim).mp target2
  have targetWidth : addressValue target.width = d 301 := by
    simp only [target, Allocation.table, addressValue_bits]
  have targetLayout : SourceLayout target (d 302) := Allocation.table_layout _ _ _ _ _
  have targetMeta : target.MetadataWidth (addressValue target.width) := by
    simpa only [target,Allocation.table,addressValue_bits] using
      Allocation.table_metadata (aliasArraySize R) (d 301) (d 302) hwidth u1.val.memory haddress
  have disjoint : c.SeparatedFrom target := Allocation.table_disjoint c rawHeap (d 301) (d 302)
    layoutC hwidth u1.val.memory (by simpa only [meta0.1] using hheap)
  have input2 : Descriptors.Inputs (inversePreparedValues c d unused) (aliasArraySize R)
      (addressValue target.width) (d 302) 0 (d 304) := by
    simpa only [hdim,target,Allocation.table,addressValue_bits] using inputs2
  have word2 : BankArray.Word u2.val 201 (tableSize (aliasArraySize R)).bits := by
    simpa only [hdim] using count2
  obtain ⟨origin2,word2⟩ := word2
  obtain ⟨c3,t,out,e3,hc3,ready3,sized,denominator,counter,result⟩ := converted_executes (aliasArraySize_pos R) (tableCoefficients c)
    (fun i => (values i).1) W hW (fun i => (values i).2.1) c target (d 302) (d 304)
    (continuationBudget W BN) padded metaC targetMeta targetLayout disjoint hshared
    (by simpa only [targetWidth] using hprepare)
    (by simpa only [targetWidth] using hslot)
    (by simpa only [targetWidth] using haddress)
    (resetParts vf) sharedWidth2 (inversePreparedValues c d unused) input2 bits2 input tape
    (tableSize (aliasArraySize R)).bits origin2 hcounterWidth u2 (by simp) word2 desc2 shared2 source2
    targetReady saved2 temp2
  rw [targetWidth] at ready3 sized hc3
  have cold : ∀ k∈Finset.Icc 530 534, t.val.tapes k=s.val.tapes k := by
    intro k hk
    have hbounds := Finset.mem_Icc.mp hk
    have hheader : k∉insert 216 PartArray.headerSlots := by
      simp only [PartArray.headerSlots,Finset.mem_insert,Finset.mem_singleton]
      omega
    exact (e3.protectsTape k (inverse_tail_protects k hk).2).trans
      ((e2.protectsTape k (inverse_tail_protects k hk).1).trans
        ((f1.tapes k hheader).trans
          (continuation k (Finset.mem_union_right _ (Finset.mem_union_right _ hk)))))
  refine ⟨c0+(c1+(c2+c3)),t,tableCoefficients c,out,e0.seq (e1.seq (e2.seq e3)),?_,values,
    ready3,sized,denominator,counter,cold,?_⟩
  · have h2 : c2 ≤ inversePrepareCost U BN B (d 301)
        (coefficientBaseWidth (countWidth B)) (tableSize (aliasArraySize R)) := by
      rw [hdim] at hc2
      unfold inversePrepareCost at hc2 ⊢
      omega
    dsimp only [U] at h2
    rw [meta0.1] at hc3
    omega
  · intro i
    rw [result i]
    have matrix : (fun i j => (tableCoefficients c (.inr (i,j))).value)=
        cachedTransitionMatrix (v 0).value (v 1).value (fun j => (RawFree.quasiParts v j).value) R := by
      funext i j
      exact (values (.inr (i,j))).2.2
    have source : (fun i => (tableCoefficients c (.inl i)).value)=
        cachedForcing (v 0).value (v 1).value (fun j => (RawFree.quasiParts v j).value) R (tableSource R a) := by
      funext i
      exact (values (.inl i)).2.2
    rw [matrix,source]
    exact (congrFun (cachedInverseApply_affine _ _ _ _ _ _) i).symm

#print axioms generated_inverse_executes

end Maxwell.Continuum.Calibration.ArrayDecodeMachine
