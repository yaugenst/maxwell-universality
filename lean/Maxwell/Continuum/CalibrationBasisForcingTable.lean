import Maxwell.Continuum.CalibrationBasisForcingBody
import Maxwell.Continuum.RationalDataflowArrayMetadata
import Maxwell.Continuum.RationalDataflowRowWriteValues

/-! Every source entry is generated from the runtime radius and countdown.
The loop needs an allocated array, but assumes none of its coefficient values.
Scratch reset keeps a uniform width bound across all iterations. -/
namespace Maxwell.Continuum.Calibration.BasisForcing
open Maxwell.Cost Maxwell.Cost.Structured FreeFiber RationalDataflow PartArray
open ArrayDecodeMachine
set_option maxHeartbeats 6000000
set_option maxRecDepth 32768
set_option exponentiation.threshold 2048
attribute [local irreducible] bank bodyCode

def tableCode (column : Fin 24) : Code := countedProgram 201 (bodyCode column)

theorem prepared_agrees (n : ℕ → ℕ) (v : ℕ → Parts) (k : ℕ) (hk : k∈ids bank) :
    preparedNaturals n v k=dataValues v k := by
  rw [preparedNaturals,ite_eq_left hk]

theorem naturalIds_counter : 201∉naturalIds := by
  intro h
  exact protected_external 201 (by simp [protectedPorts]) (Finset.mem_union_right _ h)

theorem table_executes (column : Fin 24) (R B W : ℕ) (hB : 103≤B)
    (a : Table (aliasArraySize R)) (v : ℕ → Parts) (n : ℕ → ℕ)
    (hn : ∀k∈ids bank,n k=dataValues v k) (hg : Good bank v)
    (hw : ∀k∈naturalIds,(n k).bits.length≤prepareWidth B)
    (hv : ∀k∈retained,(v k).Width B) (hRadius : R.bits.length≤B) (hR : n 311=R)
    (hm : a.MetadataWidth W) (hfit : 625≤addressValue a.width) (hsep : a.Separated)
    (input : List Bool) (tape : ℕ → Bool) (xs : List Bool) (origin : ℤ) (hlen : xs.length≤B)
    (hcount : addressValue xs=aliasArraySize R) (s : Store) (hs : NatAssign.Bank naturalIds n s.val)
    (hz : ∀k,k<5 → RationalAccumulator.Blank s.val k) (ha : a.OutputReady s)
    (hword : s.val.tapes 201=BitTape.shifted xs origin) :
    ∃cost t b vf nf finalWord,Executes input tape (tableCode column) cost s t ∧
      cost≤(aliasArraySize R+1)*(13*xs.length+15)+aliasArraySize R*bodyCost B W ∧
      b.OutputReady t ∧ sameMetadata a b ∧ Good bank vf ∧
      NatAssign.Bank naturalIds nf t.val ∧ (∀k∈ids bank,nf k=dataValues vf k) ∧
      (∀k∈naturalIds,(nf k).bits.length≤prepareWidth B) ∧
      (∀k∈retained,vf k=v k) ∧ nf 311=R ∧
      (∀k,k<5 → RationalAccumulator.Blank t.val k) ∧
      (∀i : Fin (aliasArraySize R),(b.get i).Valid ∧
        (b.get i).value=rationalRightCoupling (rationalBasisField column)
          (arrayAliasAt R i) (arrayPolarizationAt R i)) ∧
      t.val.tapes 201=BitTape.shifted finalWord origin ∧ finalWord.length=xs.length ∧
      t.val.inputHead=s.val.inputHead ∧ t.val.randomCursor=s.val.randomCursor ∧ t.val.output=s.val.output ∧ SourceFrame s.val t.val := by
  let count := aliasArraySize R
  let inv : ℕ → Store → Prop := fun remaining st => remaining≤count ∧
    ∃(vf : ℕ → Parts) (nf : ℕ → ℕ) (b : Table count),
      Good bank vf ∧ NatAssign.Bank naturalIds nf st.val ∧
      (∀k∈ids bank,nf k=dataValues vf k) ∧
      (∀k∈naturalIds,(nf k).bits.length≤prepareWidth B) ∧
      (∀k∈retained,vf k=v k) ∧ nf 311=R ∧
      (∀k,k<5 → RationalAccumulator.Blank st.val k) ∧
      b.OutputReady st ∧ sameMetadata a b ∧
      (∀i : Fin count,remaining ≤ i.val → (b.get i).Valid ∧
        (b.get i).value=rationalRightCoupling (rationalBasisField column)
          (arrayAliasAt R i) (arrayPolarizationAt R i)) ∧
      st.val.inputHead=s.val.inputHead ∧ st.val.randomCursor=s.val.randomCursor ∧ st.val.output=s.val.output ∧ SourceFrame s.val st.val
  have stable : ∀r s t,CountedShifted.Frame 201 s t → inv r s → inv r t := by
    intro r st t frame h
    obtain ⟨hr,vf,nf,b,good,words,agree,width,keep,radius,blank,output,metadata,correct,ih,random,emitted,continuation⟩ := h
    refine ⟨hr,vf,nf,b,good,?_,agree,width,keep,radius,?_,output.count_frame frame,metadata,correct,
      frame.2.1.trans ih,frame.2.2.2.1.trans random,frame.2.2.2.2.1.trans emitted,fun k hk =>
        (frame.2.2.2.2.2.1 k (continuation_outside k hk).2.2.2).trans (continuation k hk)⟩
    · intro k hk
      have he : k≠201 := fun he => naturalIds_counter (he ▸ hk)
      exact RationalAccumulator.word_of_eq (frame.2.2.2.2.2.1 k he) (words k hk)
    · intro k hk
      exact RationalAccumulator.blank_of_eq (frame.2.2.2.2.2.1 k (by omega)) (blank k hk)
  have step : ∀r ys st,inv (r+1) st → st.val.tapes 201=BitTape.shifted ys origin →
      addressValue ys=r → ys.length=xs.length →
      ∃cost out,Executes input tape (bodyCode column) cost st out ∧ inv r out ∧
        out.val.tapes 201=BitTape.shifted ys origin ∧ cost≤bodyCost B W := by
    intro r ys st h counter val length
    obtain ⟨hr,vf,nf,b,good,words,agree,width,keep,radius,blank,output,metadata,correct,ih,random,emitted,continuation⟩ := h
    have hrc : r<count := by omega
    let i : Fin count := ⟨r,hrc⟩
    have small : ∀k∈retained,(vf k).Width B := fun k hk => by rw [keep k hk];exact hv k hk
    obtain ⟨cost,t,out,exec,hcost,gout,wout,entryWidth,nout,nwidth,bout,value,preserved,zout,cout,iout,rout,eout,contout⟩ :=
      body_executes column nf vf agree good B W hB width small R i radius hRadius b
        (sameMetadata_width a b metadata W hm) (by simpa only [metadata.1] using hfit)
        (sameMetadata_separated a b metadata hsep) input tape ys (by omega) val st words blank output ⟨origin,counter⟩
    let nn := preparedNaturals (inputNaturals nf vf r) out
    have fit : (out 32).Width (addressValue b.width) := entryWidth.mono
      (by simpa only [metadata.1] using hfit)
    have correct' : ∀j : Fin count,r≤j.val → ((b.set i (out 32)).get j).Valid ∧
        ((b.set i (out 32)).get j).value=rationalRightCoupling (rationalBasisField column)
          (arrayAliasAt R j) (arrayPolarizationAt R j) := by
      intro j hj
      by_cases he : j=i
      · subst j
        rw [b.set_get i (out 32) fit]
        exact ⟨gout 32 (by unfold bank;decide),value⟩
      · rw [b.set_get_ne i j (out 32) (Ne.symm he)]
        have hne : j.val≠r := fun hh => he (Fin.ext hh)
        exact correct j (by omega)
    refine ⟨cost,t,exec,⟨by omega,out,nn,b.set i (out 32),gout,nout,prepared_agrees _ _,nwidth,
      fun k hk => (preserved k hk).trans (keep k hk),?_,zout,bout,sameMetadata_set a b i (out 32) metadata,
      correct',iout.trans ih,rout.trans random,eout.trans emitted,continuation.trans contout⟩,cout.trans counter,hcost⟩
    exact (prepared_radius _ _).trans ((input_radius nf vf r).trans radius)
  have initial : inv count s := by
    refine ⟨le_rfl,v,n,a,hg,hs,hn,hw,fun _ _ => rfl,hR,hz,ha,sameMetadata_refl a,?_,rfl,rfl,rfl,SourceFrame.refl _⟩
    intro i hi
    exact False.elim (Nat.not_le.mpr i.isLt hi)
  obtain ⟨cost,t,finalWord,exec,final,word,length,_,hcost⟩ := counted_executes_sized 201 origin
    (bodyCode column) input tape xs.length inv (fun _ => bodyCost B W)
    stable step count xs s hcount hword rfl initial
  obtain ⟨_,vf,nf,b,good,words,agree,width,keep,radius,blank,output,metadata,correct,ih,random,emitted,continuation⟩ := final
  refine ⟨cost,t,b,vf,nf,finalWord,exec,?_,output,metadata,good,words,agree,width,keep,radius,blank,
    fun i => correct i (Nat.zero_le _),word,length,ih,random,emitted,continuation⟩
  simpa only [Finset.sum_const,Finset.card_range,smul_eq_mul] using hcost

#print axioms table_executes
end Maxwell.Continuum.Calibration.BasisForcing
