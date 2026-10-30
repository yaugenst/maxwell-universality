import Maxwell.Continuum.CutoffMonomialCache

/-! One fixed outer runtime step loads a coefficient, traverses all rows,
swaps the actual cache headers, and increments its stored index. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 32768

def monomialOuterStepCode : Code := .seq monomialPrepareCode
  (.seq monomialPassCode (.seq headerSwapCode monomialIncrementCode))

theorem monomialOuterStep_executes {D W : ℕ} (a : MonomialCache D) (coeff : ℕ→Parts)
    (hw : ∀r<D,(coeff r).Width W) (hc : ∀r,(coeff r).Valid) (j : ℕ) (hj : j<D)
    (ha : a.Valid W coeff j) (xs : List Bool) (hn : addressValue xs=D)
    (hlen : xs.length≤monomialWorkingWidth D W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : a.Ready W j xs s) :
    ∃ cost t,Executes input tape monomialOuterStepCode cost s t ∧
      cost≤2^116*(D+1)*(monomialWorkingWidth D W+16)^2 ∧
      (a.next j).Ready W (j+1) xs t ∧ t.val.tapes 207=s.val.tapes 207 := by
  let B := monomialWorkingWidth D W
  have hstorage : monomialStorageWidth D W≤B := by dsimp [B,monomialWorkingWidth];omega
  have hB : 0<B := by dsimp [B,monomialWorkingWidth];omega
  have hjbits : j.bits.length≤B := by
    apply le_trans _ hlen
    rw [Nat.size_eq_bits_len]
    apply Nat.size_le.mpr
    exact lt_trans hj (by simpa only [hn] using Subtraction.addressValue_lt_pow_length xs)
  obtain ⟨ys,hylen,hy⟩ := hs.count
  obtain ⟨c0,s0,e0,hc0,r0,a0,b0,count0,z0,f0⟩ := monomialPrepare_executes a.current a.spare j hj B
    ha.currentMetadata a.bank (ha.bankWidth.mono hstorage) input tape xs ys hlen hylen hjbits s
    hs.bank hs.current hs.spare hs.index hs.saved hy hs.indexBlanks
  have r0' : RationalDataflow.Ready (Finset.range 8) (a.prepared j) s0 := r0
  have hp := a.prepared_bounds ha hj hw hc
  obtain ⟨origin,hcount0⟩ := count0
  obtain ⟨cp,s1,finalWord,ep,hcp,r1,a1,b1,z1,count1,length1⟩ := monomialPass_executes
    a.current a.spare coeff hw hc j hj ha.stored ha.currentMetadata ha.spareMetadata
    (lt_of_lt_of_le hB ha.spareSlot) ha.spareSlot ha.spareSeparated ha.disjoint
    (a.prepared j) hp.1 hp.2.1 hp.2.2.1 hp.2.2.2 input tape xs origin hlen s0 hn hcount0
    r0' a0 b0 z0
  let b' := monomialPassTable a.current a.spare (a.prepared j) D
  obtain ⟨mw,mp,mn,md,mc⟩ := monomialPassTable_metadata a.current a.spare (a.prepared j) D
  have hm : b'.MetadataWidth B :=
    ⟨by simpa only [b',mw] using ha.spareMetadata.width,
      by simpa only [b',mp] using ha.spareMetadata.basePositive,
      by simpa only [b',mn] using ha.spareMetadata.baseNegative,
      by simpa only [b',md] using ha.spareMetadata.baseDenominator,
      by simpa only [b',mc] using ha.spareMetadata.clock⟩
  have keep1 (i : ℕ) (hi : i∈([206,207,208,209,216]:List ℕ)) : s1.val.tapes i=s.val.tapes i := by
    apply (monomialPass_auxiliary_frame ep i _).trans (f0 i hi)
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide
  have swapBlank := RationalAccumulator.blank_of_eq (keep1 216 (by simp)) hs.swapBlank
  obtain ⟨ch,s2,eh,hch,r2,b2,a2,blank2,fh⟩ := headerSwap_executes a.current b' B
    ha.currentMetadata hm (Finset.range 8) (monomialPassState a.current (a.prepared j) D)
    input tape s1 r1 a1 b1 swapBlank
  have keep2 (i : ℕ) (hi : i∈([206,207,208,209]:List ℕ)) : s2.val.tapes i=s.val.tapes i := by
    apply (fh.tapes i _).trans (keep1 i (by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢;tauto))
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> decide
  have index2 := RationalAccumulator.word_of_eq (keep2 208 (by simp)) hs.index
  have one2 := RationalAccumulator.word_of_eq (keep2 209 (by simp)) hs.one
  obtain ⟨ci,t,ei,hci,index3,one3,zt,fi⟩ := monomialIncrement_executes j input tape s2 index2 one2 r2.2
  have fi' := monomialIncrement_frame fi
  have r3 := monomialControl_rational_frame r2 fi' zt
  have b3 := monomialControl_table_frame b2 fi' zt
  have a3 := monomialControl_output_frame a2 fi' b3.scratch b3.seven
  have z3 : ∀i∈RowIndex.ids,RationalAccumulator.Blank t.val i := by
    intro i hi
    apply RationalAccumulator.blank_of_eq ((fi.tapes i _).trans (fh.tapes i _)) (z1 i hi)
    all_goals
      simp only [RowIndex.ids,Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl <;> decide
  have count3 : BankArray.Word t.val 201 finalWord :=
    BankArray.word_of_eq ((fi.tapes 201 (by decide)).trans (fh.tapes 201 (by decide))) ⟨origin,count1⟩
  have saved3 : BankArray.Word t.val 206 xs := BankArray.word_of_eq
    ((fi.tapes 206 (by decide)).trans (keep2 206 (by simp))) hs.saved
  refine ⟨c0+(cp+(ch+ci)),t,e0.seq (ep.seq (eh.seq ei)),?_,
    ⟨r3,b3,a3,z3,RationalAccumulator.blank_of_eq (fi.tapes 216 (by decide)) blank2,
      saved3,⟨finalWord,by omega,count3⟩,index3,one3⟩,
    (fi.tapes 207 (by decide)).trans (keep2 207 (by simp))⟩
  have hcp' : cp≤(D+1)*(13*B+15)+D*(2^112*(B+16)^2) := hcp.trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega : 13*xs.length+15≤13*B+15)) _)
  have hci' : ci≤200*(B+5) := hci.trans (Nat.mul_le_mul_left _ (by omega))
  have hsmall : c0+ch+ci≤2^34*(B+16)^2 := by
    norm_num at hc0 hch hci' ⊢
    nlinarith only [hc0,hch,hci',Nat.zero_le B]
  have hcount : (D+1)*(13*B+15)≤16*(D+1)*(B+16)^2 := by
    have h := Nat.mul_le_mul_left (D+1) (show 13*B+15≤16*(B+16)^2 by nlinarith)
    nlinarith only [h]
  have hrow : D*(2^112*(B+16)^2)≤2^112*(D+1)*(B+16)^2 := by
    nlinarith only [Nat.zero_le ((B+16)^2)]
  have hsmall' := Nat.mul_le_mul_right ((B+16)^2) (show 2^34≤2^34*(D+1) by nlinarith)
  change c0+(cp+(ch+ci))≤2^116*(D+1)*(B+16)^2
  norm_num at hsmall hcount hrow hsmall' ⊢
  nlinarith only [hcp',hsmall,hcount,hrow,hsmall']

#print axioms monomialOuterStep_executes
end Maxwell.Continuum.Calibration.RawCutoff
