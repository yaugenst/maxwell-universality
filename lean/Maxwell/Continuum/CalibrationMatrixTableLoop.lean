import Maxwell.Continuum.CalibrationMatrixEmission
import Maxwell.Continuum.RationalDataflowRowWriteValues

/-! The fixed runtime loop generates every actual cached transition entry.
Only the allocated table and physical scalar inputs are supplied; no matrix
entry, branch trace, or per-iteration width certificate is an input. -/

namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine

open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384
set_option exponentiation.threshold 1024

def sameMetadata {T : ℕ} (a b : PartArray.Table T) : Prop :=
  b.width=a.width ∧ b.basePositive=a.basePositive ∧ b.baseNegative=a.baseNegative ∧
    b.baseDenominator=a.baseDenominator ∧ b.clock=a.clock

theorem sameMetadata_refl {T : ℕ} (a : PartArray.Table T) : sameMetadata a a :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩
theorem sameMetadata_set {T : ℕ} (a b : PartArray.Table T) (i : Fin T) (x : Parts)
    (h : sameMetadata a b) : sameMetadata a (b.set i x) := h
theorem sameMetadata_width {T : ℕ} (a b : PartArray.Table T) (h : sameMetadata a b)
    (W : ℕ) (ha : a.MetadataWidth W) : b.MetadataWidth W :=
  ⟨by simpa only [h.1] using ha.width,by simpa only [h.2.1] using ha.basePositive,
    by simpa only [h.2.2.1] using ha.baseNegative,by simpa only [h.2.2.2.1] using ha.baseDenominator,
    by simpa only [h.2.2.2.2] using ha.clock⟩
theorem sameMetadata_separated {T : ℕ} (a b : PartArray.Table T) (h : sameMetadata a b)
    (ha : a.Separated) : b.Separated := by
  simpa only [PartArray.Table.Separated,h.1,h.2.1,h.2.2.1,h.2.2.2.1] using ha

def flatRow (R : ℕ) (k : Fin (aliasArraySize R*aliasArraySize R)) : Fin (aliasArraySize R) :=
  ⟨k.val/aliasArraySize R,(Nat.div_lt_iff_lt_mul (aliasArraySize_pos R)).mpr k.isLt⟩
def flatColumn (R : ℕ) (k : Fin (aliasArraySize R*aliasArraySize R)) : Fin (aliasArraySize R) :=
  ⟨k.val%aliasArraySize R,Nat.mod_lt _ (aliasArraySize_pos R)⟩
def matrixSlot {T : ℕ} (R : ℕ) (hT : aliasArraySize R+aliasArraySize R*aliasArraySize R≤T)
    (k : Fin (aliasArraySize R*aliasArraySize R)) : Fin T :=
  ⟨aliasArraySize R+k.val,by have := k.isLt; omega⟩
def matrixTableCode : Code := countedProgram 201 emissionCode

theorem emissionNaturals_agrees (v : ℕ→Parts) (n : ℕ→ℕ) (index k : ℕ)
    (hk : k∈ids RawFree.neighborRegisters) :
    emissionNaturals v n index k=dataValues (emissionParts v n index) k := by
  rw [emissionNaturals,matrixEntryNaturals,ite_eq_left hk]
  rfl

theorem matrixTable_executes {T : ℕ} (a : PartArray.Table T) (R B W : ℕ) (hB : 101≤B)
    (hT : aliasArraySize R+aliasArraySize R*aliasArraySize R≤T)
    (v : ℕ→Parts) (n : ℕ→ℕ)
    (hn : ∀ k∈ids RawFree.neighborRegisters, n k=dataValues v k)
    (hw : ∀ k∈emissionIds, (n k).bits.length≤emissionWidth B)
    (hp : ∀ k∈matrixParameters, (v k).Width B ∧ (v k).Valid)
    (hR : R.bits.length≤B) (hradius : n 311=R)
    (hmeta : a.MetadataWidth W) (hfit : emissionWidth B≤addressValue a.width) (hsep : a.Separated)
    (htbox : (3:ℝ)≤(v 0).value)
    (hEbox : (7:ℝ)≤(v 1).value ∧ ((v 1).value:ℝ)≤8)
    (hrbox : ∀ k, |((RawFree.quasiParts v k).value:ℝ)|≤1/16)
    (input : List Bool) (tape : ℕ→Bool) (xs : List Bool) (origin : ℤ) (hlen : xs.length≤B)
    (hcount : addressValue xs=aliasArraySize R*aliasArraySize R)
    (s : Store) (hs : NatAssign.Bank emissionIds n s.val)
    (hz : ∀ k, k<5 → RationalAccumulator.Blank s.val k)
    (ha : a.OutputReady s) (hword : s.val.tapes 201=BitTape.shifted xs origin) :
    ∃ (cost : ℕ) (t : Store) (b : PartArray.Table T) (vf : ℕ→Parts) (nf : ℕ→ℕ) (finalWord : List Bool),
      Executes input tape matrixTableCode cost s t ∧
      cost≤(aliasArraySize R*aliasArraySize R+1)*(13*xs.length+15)+
        (aliasArraySize R*aliasArraySize R)*(2^600*(emissionWidth B+W+10)^2) ∧
      b.OutputReady t ∧ sameMetadata a b ∧
      NatAssign.Bank emissionIds nf t.val ∧
      (∀ k∈ids RawFree.neighborRegisters, nf k=dataValues vf k) ∧
      (∀ k∈emissionIds, (nf k).bits.length≤emissionWidth B) ∧
      (∀ k∈matrixParameters, vf k=v k) ∧ nf 311=R ∧
      (∀ k, k<5 → RationalAccumulator.Blank t.val k) ∧
      (∀ k : Fin (aliasArraySize R*aliasArraySize R),
        (b.get (matrixSlot R hT k)).Valid ∧
        (b.get (matrixSlot R hT k)).value=cachedTransitionMatrix (v 0).value (v 1).value
          (fun j => (RawFree.quasiParts v j).value) R (flatRow R k) (flatColumn R k)) ∧
      (∀ i : Fin T, i.val<aliasArraySize R ∨ aliasArraySize R+aliasArraySize R*aliasArraySize R ≤ i.val →
        b.get i=a.get i) ∧
      t.val.tapes 201=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length ∧
      (∀ k∈([200,202,203,204,205]:List ℕ), t.val.tapes k=s.val.tapes k) ∧
      ContinuationFrame s.val t.val := by
  let count := aliasArraySize R*aliasArraySize R
  let inv : ℕ→Store→Prop := fun remaining st => remaining≤count ∧
    ∃ (vf : ℕ→Parts) (nf : ℕ→ℕ) (b : PartArray.Table T),
      NatAssign.Bank emissionIds nf st.val ∧
      (∀ k∈ids RawFree.neighborRegisters, nf k=dataValues vf k) ∧
      (∀ k∈emissionIds, (nf k).bits.length≤emissionWidth B) ∧
      (∀ k∈matrixParameters, vf k=v k) ∧ nf 311=R ∧
      (∀ k, k<5 → RationalAccumulator.Blank st.val k) ∧
      b.OutputReady st ∧ sameMetadata a b ∧
      (∀ k : Fin count, remaining≤k.val →
        (b.get (matrixSlot R hT k)).Valid ∧
        (b.get (matrixSlot R hT k)).value=cachedTransitionMatrix (v 0).value (v 1).value
          (fun j => (RawFree.quasiParts v j).value) R (flatRow R k) (flatColumn R k)) ∧
      (∀ i : Fin T, i.val<aliasArraySize R ∨ aliasArraySize R+count ≤ i.val → b.get i=a.get i) ∧
      (∀ k∈([200,202,203,204,205]:List ℕ), st.val.tapes k=s.val.tapes k) ∧
      ContinuationFrame s.val st.val
  have stable : ∀ r s t, CountedShifted.Frame 201 s t → inv r s → inv r t := by
    intro r s t frame hh
    obtain ⟨hcount,vf,nf,b,bank,agree,width,parameters,radius,blank,outReady,metadata,correct,outside,headers,continuation⟩ := hh
    refine ⟨hcount,vf,nf,b,?_,agree,width,parameters,radius,?_,outReady.count_frame frame,
      metadata,correct,outside,?_,fun k hk => (frame.2.2.2.2.2.1 k (continuation_external k hk).2.2.2.1).trans (continuation k hk)⟩
    · intro k hk
      have hne : k≠201 := by intro he; subst k; exact (by decide : 201∉emissionIds) hk
      exact RationalAccumulator.word_of_eq (frame.2.2.2.2.2.1 k hne) (bank k hk)
    · intro k hk
      exact RationalAccumulator.blank_of_eq (frame.2.2.2.2.2.1 k (by omega)) (blank k hk)
    · intro k hk
      have hne : k≠201 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        omega
      exact (frame.2.2.2.2.2.1 k hne).trans (headers k hk)
  have step : ∀ r ys st, inv (r+1) st → st.val.tapes 201=BitTape.shifted ys origin →
      addressValue ys=r → ys.length=xs.length →
      ∃ cost out, Executes input tape emissionCode cost st out ∧ inv r out ∧
        out.val.tapes 201=BitTape.shifted ys origin ∧ cost≤2^600*(emissionWidth B+W+10)^2 := by
    intro r ys st hh hcounter hval hlength
    obtain ⟨hrcount,vf,nf,b,bank,agree,width,parameters,radius,blank,outReady,metadata,correct,outside,headers,continuation⟩ := hh
    have hr : r<count := by omega
    let k : Fin count := ⟨r,hr⟩
    let slot : Fin T := matrixSlot R hT k
    have paramWidth : ∀ j∈matrixParameters, (vf j).Width B ∧ (vf j).Valid := by
      intro j hj
      rw [parameters j hj]
      exact hp j hj
    have p0 := parameters 0 (by decide)
    have p1 := parameters 1 (by decide)
    have quasi : RawFree.quasiParts vf=RawFree.quasiParts v := by
      funext j
      fin_cases j
      · exact parameters 16 (by decide)
      · exact parameters 17 (by decide)
      · exact parameters 18 (by decide)
    obtain ⟨cost,out,he,hcost,bank',ready',good',width',table',value,blank',counter',headers',continuation'⟩ :=
      emission_executes b slot vf nf B W hB agree width paramWidth (by simpa only [radius] using hR)
        (sameMetadata_width a b metadata W hmeta) (by simpa only [metadata.1] using hfit)
        (sameMetadata_separated a b metadata hsep) R (flatRow R k) (flatColumn R k) r radius rfl rfl rfl
        (by simpa only [p0] using htbox) (by simpa only [p1] using hEbox)
        (by simpa only [quasi] using hrbox) input tape ys (by omega) hval st bank blank outReady ⟨origin,hcounter⟩
    let wf := emissionParts vf nf r
    let nn := emissionNaturals vf nf r
    have agree' : ∀ j∈ids RawFree.neighborRegisters, nn j=dataValues wf j := emissionNaturals_agrees vf nf r
    have fit : (wf 12).Width (addressValue b.width) :=
      (data_width_all _ nn wf (emissionWidth B) agree'
        (fun j hj => width' j (emissionIds_parts hj)) 12 (by decide)).mono (by simpa only [metadata.1] using hfit)
    have exactValue : (wf 12).value=cachedTransitionMatrix (v 0).value (v 1).value
        (fun j => (RawFree.quasiParts v j).value) R (flatRow R k) (flatColumn R k) := by
      simpa only [p0,p1,quasi] using value
    have correct' : ∀ j : Fin count, r≤j.val →
        ((b.set slot (wf 12)).get (matrixSlot R hT j)).Valid ∧
        ((b.set slot (wf 12)).get (matrixSlot R hT j)).value=cachedTransitionMatrix (v 0).value (v 1).value
          (fun l => (RawFree.quasiParts v l).value) R (flatRow R j) (flatColumn R j) := by
      intro j hj
      by_cases heq : j=k
      · subst j
        rw [b.set_get slot (wf 12) fit]
        exact ⟨good' 12 (by decide),exactValue⟩
      · have hne : slot≠matrixSlot R hT j := by
          intro heq'
          have hvals := congrArg Fin.val heq'
          apply heq
          apply Fin.ext
          change aliasArraySize R+k.val=aliasArraySize R+j.val at hvals
          omega
        rw [b.set_get_ne slot (matrixSlot R hT j) (wf 12) hne]
        apply correct j
        have hneq : j.val≠r := fun heq' => heq (Fin.ext heq')
        omega
    have outside' : ∀ i : Fin T, i.val<aliasArraySize R ∨ aliasArraySize R+count ≤ i.val →
        (b.set slot (wf 12)).get i=a.get i := by
      intro i hi
      have hne : slot≠i := by
        intro heq
        have he := congrArg Fin.val heq
        change aliasArraySize R+r=i.val at he
        omega
      rw [b.set_get_ne slot i (wf 12) hne]
      exact outside i hi
    refine ⟨cost,out,he,⟨by omega,wf,nn,b.set slot (wf 12),bank',agree',width',?_,?_,blank',
      table',sameMetadata_set a b slot (wf 12) metadata,correct',outside',fun k hk => (headers' k hk).trans (headers k hk),continuation.trans continuation'⟩,
      counter'.trans hcounter,hcost⟩
    · intro j hj
      exact (emissionParts_parameter vf nf r j hj).trans (parameters j hj)
    · exact (emissionNaturals_radius vf nf r).trans radius
  have initial : inv count s := by
    refine ⟨le_rfl,v,n,a,hs,hn,hw,fun _ _ => rfl,hradius,hz,ha,sameMetadata_refl a,?_,fun _ _ => rfl,fun _ _ => rfl,ContinuationFrame.refl _⟩
    intro k hk
    exact False.elim (Nat.not_le.mpr k.isLt hk)
  obtain ⟨cost,t,finalWord,he,hfinal,hword',hfinalLength,_,hcost⟩ := counted_executes_sized 201 origin
    emissionCode input tape xs.length inv (fun _ => 2^600*(emissionWidth B+W+10)^2)
    stable step count xs s hcount hword rfl initial
  obtain ⟨_,vf,nf,b,bank,agree,width,parameters,radius,blank,outReady,metadata,correct,outside,headers,continuation⟩ := hfinal
  refine ⟨cost,t,b,vf,nf,finalWord,he,?_,outReady,metadata,bank,agree,width,parameters,radius,blank,
    fun k => correct k (Nat.zero_le _),outside,hword',hfinalLength,headers,continuation⟩
  simpa only [Finset.sum_const,Finset.card_range,smul_eq_mul] using hcost

#print axioms matrixTable_executes

end Maxwell.Continuum.Calibration.ArrayDecodeMachine
