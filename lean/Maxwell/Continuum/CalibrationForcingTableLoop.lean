import Maxwell.Continuum.CalibrationForcingEmission

/-! One fixed runtime loop emits the entire literal forcing vector from
the actual source table. No precomputed forcing table is supplied. -/

namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 6500000
set_option maxRecDepth 16384
set_option exponentiation.threshold 2048

def sourceSlot {T : ℕ} (R : ℕ) (hT : aliasArraySize R≤T) (i : Fin (aliasArraySize R)) : Fin T :=
  ⟨i.val,i.isLt.trans_le hT⟩
def forcingTableCode : Code := countedProgram 201 forcingEmissionCode

theorem sameMetadata_disjoint {S T : ℕ} (a : PartArray.Table S) (b c : PartArray.Table T)
    (h : sameMetadata b c) (ha : a.SeparatedFrom b) : a.SeparatedFrom c := by
  simpa only [PartArray.Table.SeparatedFrom,h.1,h.2.1,h.2.2.1,h.2.2.2.1] using ha

theorem forcingTable_executes {T : ℕ} (R : ℕ) (a : PartArray.Table (aliasArraySize R))
    (b : PartArray.Table T) (B W : ℕ) (hB : 2≤B) (hT : aliasArraySize R≤T)
    (v : ℕ→Parts) (n : ℕ→ℕ)
    (hn : ∀ k∈ids RawFree.neighborRegisters, n k=dataValues v k)
    (hw : ∀ k∈emissionIds, (n k).bits.length≤forcingEmissionWidth B)
    (hp : ∀ k∈matrixParameters, (v k).Width B ∧ (v k).Valid)
    (hR : R.bits.length≤B) (hradius : n 311=R)
    (haValid : ∀ i, (a.get i).Valid) (haMeta : a.MetadataWidth B) (hbMeta : b.MetadataWidth W)
    (hfit : forcingEmissionWidth B≤addressValue b.width) (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (ht : (3:ℝ)≤(v 0).value) (hE : (7:ℝ)≤(v 1).value ∧ ((v 1).value:ℝ)≤8)
    (hr : ∀ k, |((RawFree.quasiParts v k).value:ℝ)|≤1/16)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ) (hlen : xs.length≤B)
    (hcount : addressValue xs=aliasRowCount R) (s : Store) (hs : NatAssign.Bank emissionIds n s.val)
    (hz : ∀ k, k<5 → RationalAccumulator.Blank s.val k)
    (ha : a.Ready s) (hb : b.OutputReady s) (hword : s.val.tapes 201=BitTape.shifted xs origin) :
    ∃ (cost : ℕ) (t : Store) (c : PartArray.Table T) (vf : ℕ→Parts) (nf : ℕ→ℕ) (finalWord : List Bool),
      Executes input tape forcingTableCode cost s t ∧
      cost≤(aliasRowCount R+1)*(13*xs.length+15)+aliasRowCount R*(2^1120*(forcingEmissionWidth B+W+10)^2) ∧
      a.Ready t ∧ c.OutputReady t ∧ sameMetadata b c ∧
      NatAssign.Bank emissionIds nf t.val ∧
      (∀ k∈ids RawFree.neighborRegisters, nf k=dataValues vf k) ∧
      (∀ k∈emissionIds, (nf k).bits.length≤forcingEmissionWidth B) ∧
      (∀ k∈matrixParameters, vf k=v k) ∧ nf 311=R ∧
      (∀ k, k<5 → RationalAccumulator.Blank t.val k) ∧
      (∀ i : Fin (aliasArraySize R), (c.get (sourceSlot R hT i)).Valid ∧
        (c.get (sourceSlot R hT i)).value=cachedForcing (v 0).value (v 1).value
          (fun j => (RawFree.quasiParts v j).value) R (tableSource R a) i) ∧
      (∀ i : Fin T, aliasArraySize R≤ i.val → c.get i=b.get i) ∧
      t.val.tapes 201=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length ∧ ContinuationFrame s.val t.val := by
  let count := aliasRowCount R
  let inv : ℕ→Store→Prop := fun remaining st => remaining≤count ∧
    ∃ (vf : ℕ→Parts) (nf : ℕ→ℕ) (c : PartArray.Table T),
      NatAssign.Bank emissionIds nf st.val ∧
      (∀ k∈ids RawFree.neighborRegisters, nf k=dataValues vf k) ∧
      (∀ k∈emissionIds, (nf k).bits.length≤forcingEmissionWidth B) ∧
      (∀ k∈matrixParameters, vf k=v k) ∧ nf 311=R ∧
      (∀ k, k<5 → RationalAccumulator.Blank st.val k) ∧
      a.Ready st ∧ c.OutputReady st ∧ sameMetadata b c ∧
      (∀ i : Fin (aliasArraySize R), 3*remaining≤ i.val →
        (c.get (sourceSlot R hT i)).Valid ∧
        (c.get (sourceSlot R hT i)).value=cachedForcing (v 0).value (v 1).value
          (fun j => (RawFree.quasiParts v j).value) R (tableSource R a) i) ∧
      (∀ i : Fin T, aliasArraySize R≤ i.val → c.get i=b.get i) ∧
      ContinuationFrame s.val st.val
  have stable : ∀ r s t, CountedShifted.Frame 201 s t → inv r s → inv r t := by
    intro r s t frame hh
    obtain ⟨hcount,vf,nf,c,bank,agree,width,parameters,radius,blank,inReady,outReady,metadata,correct,outside,continuation⟩ := hh
    refine ⟨hcount,vf,nf,c,?_,agree,width,parameters,radius,?_,inReady.count_frame frame,
      outReady.count_frame frame,metadata,correct,outside,
      fun k hk => (frame.2.2.2.2.2.1 k (continuation_external k hk).2.2.2.1).trans (continuation k hk)⟩
    · intro k hk
      have hne : k≠201 := by intro he; subst k; exact (by decide : 201∉emissionIds) hk
      exact RationalAccumulator.word_of_eq (frame.2.2.2.2.2.1 k hne) (bank k hk)
    · intro k hk
      exact RationalAccumulator.blank_of_eq (frame.2.2.2.2.2.1 k (by omega)) (blank k hk)
  have step : ∀ r ys st, inv (r+1) st → st.val.tapes 201=BitTape.shifted ys origin →
      addressValue ys=r → ys.length=xs.length →
      ∃ cost out, Executes input tape forcingEmissionCode cost st out ∧ inv r out ∧
        out.val.tapes 201=BitTape.shifted ys origin ∧ cost≤2^1120*(forcingEmissionWidth B+W+10)^2 := by
    intro r ys st hh hcounter hval hlength
    obtain ⟨hrcount,vf,nf,c,bank,agree,width,parameters,radius,blank,inReady,outReady,metadata,correct,outside,continuation⟩ := hh
    have hrow : r<count := by omega
    let row : Fin count := ⟨r,hrow⟩
    have paramWidth : ∀ k∈matrixParameters, (vf k).Width B ∧ (vf k).Valid := by
      intro k hk
      rw [parameters k hk]
      exact hp k hk
    have p0 := parameters 0 (by decide)
    have p1 := parameters 1 (by decide)
    have quasi : RawFree.quasiParts vf=RawFree.quasiParts v := by
      funext k
      fin_cases k
      · exact parameters 16 (by decide)
      · exact parameters 17 (by decide)
      · exact parameters 18 (by decide)
    obtain ⟨cost,out,he,hcost,bank',ready',good',width',inReady',outReady',value,blank',counter',continuation'⟩ :=
      forcingEmission_executes R a c row hT vf nf B W hB agree width paramWidth
        (by simpa only [radius] using hR) radius haValid haMeta (sameMetadata_width b c metadata W hbMeta)
        (by simpa only [metadata.1] using hfit) (sameMetadata_separated b c metadata hsep)
        (sameMetadata_disjoint a b c metadata hdisjoint)
        (by simpa only [p0] using ht) (by simpa only [p1] using hE)
        (by simpa only [quasi] using hr) input tape ys (by omega) hval st bank blank inReady outReady ⟨origin,hcounter⟩
    let wf := forcingComputedParts R a vf nf r
    let nn := forcingComputedNaturals R a vf nf r
    let d := PartArray.rowWriteTable 3 r forcingWritePlan wf c
    have agree' : ∀ k∈ids RawFree.neighborRegisters, nn k=dataValues wf k := forcingComputed_agrees R a vf nf r
    have fit : ∀ j : Fin 3, (wf (37+j.val)).Width (addressValue c.width) := by
      intro j
      have hj : 37+j.val∈RawFree.neighborRegisters := by change 37+j.val∈Finset.range 41; simp; omega
      exact (data_width_all _ nn wf (forcingEmissionWidth B) agree'
        (fun k hk => width' k (emissionIds_parts hk)) _ hj).mono (by simpa only [metadata.1] using hfit)
    have exactValue : ∀ j : Fin 3, (wf (37+j.val)).value=cachedForcing (v 0).value (v 1).value
        (fun k => (RawFree.quasiParts v k).value) R (tableSource R a) (polarizationRow R row j) := by
      intro j
      simpa only [p0,p1,quasi] using value j
    have correct' : ∀ i : Fin (aliasArraySize R), 3*r≤ i.val →
        (d.get (sourceSlot R hT i)).Valid ∧
        (d.get (sourceSlot R hT i)).value=cachedForcing (v 0).value (v 1).value
          (fun k => (RawFree.quasiParts v k).value) R (tableSource R a) i := by
      intro i hi
      by_cases hcurrent : i.val<3*r+3
      · let j : Fin 3 := ⟨i.val%3,Nat.mod_lt _ (by decide)⟩
        have heq : polarizationRow R row j=i := by apply Fin.ext; dsimp [polarizationRow,row,j]; omega
        have index : (sourceSlot R hT i).val=3*r+j.val := by dsimp [sourceSlot,j]; omega
        rw [forcingWrite_get c r wf j (sourceSlot R hT i) index fit]
        refine ⟨good' (37+j.val) ?_,?_⟩
        · change 37+j.val∈Finset.range 41
          simp
          omega
        · rw [← heq]
          exact exactValue j
      · rw [forcingWrite_unchanged c r wf (sourceSlot R hT i) (Or.inr (by exact Nat.le_of_not_gt hcurrent))]
        exact correct i (by omega)
    have outside' : ∀ i : Fin T, aliasArraySize R≤ i.val → d.get i=b.get i := by
      intro i hi
      have hn : 3*(r+1)≤aliasArraySize R := by
        change 3*(r+1)≤aliasRowCount R*3
        dsimp [count] at hrow
        omega
      rw [forcingWrite_unchanged c r wf i (Or.inr (by omega))]
      exact outside i hi
    refine ⟨cost,out,he,⟨by omega,wf,nn,d,bank',agree',width',?_,?_,blank',inReady',outReady',
      forcingWrite_metadata b c r wf metadata,correct',outside',continuation.trans continuation'⟩,counter'.trans hcounter,hcost⟩
    · intro k hk
      exact (forcingComputed_parameter R a vf nf r k hk).trans (parameters k hk)
    · exact (forcingComputed_radius R a vf nf r).trans radius
  have initial : inv count s := by
    refine ⟨le_rfl,v,n,b,hs,hn,hw,fun _ _ => rfl,hradius,hz,ha,hb,sameMetadata_refl b,?_,fun _ _ => rfl,ContinuationFrame.refl _⟩
    intro i hi
    have hi' := i.isLt
    change i.val<aliasRowCount R*3 at hi'
    dsimp [count] at hi
    omega
  obtain ⟨cost,t,finalWord,he,hfinal,hword',hfinalLength,_,hcost⟩ := counted_executes_sized 201 origin
    forcingEmissionCode input tape xs.length inv (fun _ => 2^1120*(forcingEmissionWidth B+W+10)^2)
    stable step count xs s hcount hword rfl initial
  obtain ⟨_,vf,nf,c,bank,agree,width,parameters,radius,blank,inReady,outReady,metadata,correct,outside,continuation⟩ := hfinal
  refine ⟨cost,t,c,vf,nf,finalWord,he,?_,inReady,outReady,metadata,bank,agree,width,parameters,radius,blank,
    fun i => correct i (by omega),outside,hword',hfinalLength,continuation⟩
  simpa only [Finset.sum_const,Finset.card_range,smul_eq_mul] using hcost

#print axioms forcingTable_executes

end Maxwell.Continuum.Calibration.ArrayDecodeMachine
