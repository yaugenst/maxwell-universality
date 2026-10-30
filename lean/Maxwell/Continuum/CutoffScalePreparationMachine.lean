import Maxwell.Continuum.CutoffScalePreparation
import Maxwell.Continuum.RationalDataflowWordReplace
import Maxwell.Cost.BankArray.Decrement

/-! The scale initializer executes its seven constant writes, stored-count
copy and decrement, power/odd loop, cleanup, and count restoration. -/
namespace Maxwell.Continuum.Calibration.RawCutoff
open RationalDataflow RationalDataflow.PartArray Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 3500000
set_option maxRecDepth 32768

def scalePreparationCode : Code := .seq scalePrepareInitial.code
  (.seq (WordReplace.code 206 201) (.seq (BankArray.decrementCode 201)
    (.seq (countedProgram 201 scalePrepareBody.code)
      (.seq (NatAssign.code (literalStage 4 (Parts.literal 0))) (WordReplace.code 206 201)))))

def scalePreparationCost (n W len oldlen : ℕ) : ℕ :=
  7*operationCost (128*(W+4))+1+(6*oldlen+15*len+21)+(29*len+32)+
    n*(13*len+15)+(n-1)*(2*operationCost (64*(n+1))+1)+
      stageCost (8*(n+1))+(21*len+21)

theorem scalePreparation_executes (n W : ℕ) (hnpos : 0<n)
    (v : ℕ→Parts) (hv : WidthBank scaleSlots W v) (hg : Good scaleSlots v)
    (input : List Bool) (tape : ℕ→Bool) (xs ys : List Bool) (hn : addressValue xs=n)
    (s : Store) (hs : RationalDataflow.Ready scaleSlots v s)
    (hsaved : BankArray.Word s.val 206 xs) (hcount : BankArray.Word s.val 201 ys) :
    ∃ cost t,Executes input tape scalePreparationCode cost s t ∧
      cost≤scalePreparationCost n W xs.length ys.length ∧
      RationalDataflow.Ready scaleSlots (scaleInitial n) t ∧
      BankArray.Word t.val 206 xs ∧ BankArray.Word t.val 201 xs := by
  have outside201 : 201∉workspace scaleSlots := outside_workspace _ _ (by decide)
  have outside206 : 206∉workspace scaleSlots := outside_workspace _ _ (by decide)
  have hlit : scalePrepareInitial.LiteralsFit 3 := by
    norm_num [scalePrepareInitial,Control.prepend,Control.LiteralsFit,Instruction.LiteralFits,
      Parts.Width,Parts.literal]
    decide
  have htrace : scalePrepareInitial.WidthTrace scaleSlots (128*(W+4)) v := by
    exact scalePrepareInitial.automatic_widthTrace scaleSlots scalePrepareInitial_valid v (W+3)
      (hv.mono (by omega)) (hlit.mono (by omega))
  obtain ⟨c0,s0,e0,hc0,r0,f0⟩ := scalePrepareInitial.executes scaleSlots scalePrepareInitial_valid v
    (128*(W+4)) htrace hg (by trivial) input tape s hs
  have r0' : RationalDataflow.Ready scaleSlots (scalePrepareState 0 v) s0 := by
    simpa only [scalePrepareInitial_state] using r0
  have saved0 := BankArray.word_of_eq (f0.tapes 206 outside206) hsaved
  have count0 := BankArray.word_of_eq (f0.tapes 201 outside201) hcount
  obtain ⟨s1,e1,count1,f1⟩ := WordReplace.executes 206 201 (by decide) input tape xs ys s0 saved0 count0
  have r1 := r0'.wordReplace_frame outside201 f1
  have saved1 := BankArray.word_of_eq (f1.2.2.2.2.2.1 206 (by decide)) saved0
  obtain ⟨cd,s2,hcd,ed,count2,_,fd,_⟩ := BankArray.decrement_bank 201 input tape xs
    (by simpa only [hn] using hnpos) s1 count1
  have r2 : RationalDataflow.Ready scaleSlots (scalePrepareState 0 v) s2 := by
    constructor
    · intro i hi
      apply RationalAccumulator.word_of_eq (fd i _) (r1.1 i hi)
      intro he
      exact outside201 (he ▸ Finset.mem_union_right _ hi)
    · intro i hi
      exact RationalAccumulator.blank_of_eq (fd i (by omega)) (r1.2 i hi)
  have saved2 := BankArray.word_of_eq (fd 206 (by decide)) saved1
  have count2' : BankArray.Word s2.val 201 (n-1).bits := by simpa only [hn] using count2
  obtain ⟨origin,count2'⟩ := count2'
  have hloopwidth (k : ℕ) (hk : k<n-1) : scalePrepareBody.WidthTrace scaleSlots (64*(n+1))
      (iterateControl scalePrepareBody (scalePrepareState 0 v) k) :=
    (scalePrepareBody_widthTrace (n-1) k hk v).mono (by omega)
  have hloopgood (k : ℕ) (_hk : k<n-1) : Good scaleSlots
      (iterateControl scalePrepareBody (scalePrepareState 0 v) k) := by
    rw [scalePrepare_iterate]
    exact scalePrepareState_good k v
  obtain ⟨cl,s3,finalWord,el,r3,count3,length3,hcl⟩ := controlCounted_executes scaleSlots 201 outside201
    scalePrepareBody scalePrepareBody_valid (n-1) (64*(n+1)) (scalePrepareState 0 v)
    hloopwidth hloopgood (by intros;trivial) input tape (n-1).bits origin s2
    (addressValue_bits _) count2' r2
  have r3' : RationalDataflow.Ready scaleSlots (scalePrepareState (n-1) v) s3 := by
    simpa only [scalePrepare_iterate] using r3
  have saved3 : BankArray.Word s3.val 206 xs := BankArray.word_of_eq
    (el.protectsTape 206 (by decide)) saved2
  obtain ⟨cc,s4,ec,hcc,r4,fc⟩ := literal_executes scaleSlots 4 (by decide) (Parts.literal 0)
    (scalePrepareState (n-1) v) (8*(n+1))
    ((Parts.literal_width RationalWords.width_zero').mono (by omega))
    (scalePrepareState_width n (n-1) (Nat.sub_le _ _) v) input tape s3 r3'
  have saved4 := BankArray.word_of_eq (fc.tapes 206 outside206) saved3
  have count4 : BankArray.Word s4.val 201 finalWord :=
    BankArray.word_of_eq (fc.tapes 201 outside201) ⟨origin,count3⟩
  obtain ⟨t,e5,count5,f5⟩ := WordReplace.executes 206 201 (by decide) input tape xs finalWord s4 saved4 count4
  have rt := (r4.wordReplace_frame outside201 f5).congr (scalePrepare_finish n v)
  have bitsBound : (n-1).bits.length≤xs.length := by
    rw [Nat.size_eq_bits_len]
    apply Nat.size_le.mpr
    exact lt_of_le_of_lt (Nat.sub_le _ _) (by simpa only [hn] using Subtraction.addressValue_lt_pow_length xs)
  have hc0' : c0≤7*operationCost (128*(W+4))+1 := hc0
  have hcl' : cl≤n*(13*xs.length+15)+(n-1)*(2*operationCost (64*(n+1))+1) := by
    have he : n-1+1=n := by omega
    change cl≤n*(13*xs.length+15)+(n-1)*(2*operationCost (64*(n+1))+1)
    apply hcl.trans
    change (n-1+1)*(13*(n-1).bits.length+15)+(n-1)*(2*operationCost (64*(n+1))+1)≤_
    rw [he]
    gcongr
  refine ⟨c0+((6*ys.length+15*xs.length+21)+(cd+(cl+(cc+(6*finalWord.length+15*xs.length+21))))),
    t,e0.seq (e1.seq (ed.seq (el.seq (ec.seq e5)))),?_,rt,
    BankArray.word_of_eq (f5.2.2.2.2.2.1 206 (by decide)) saved4,count5⟩
  unfold scalePreparationCost
  omega

theorem scalePreparation_protects_memory : scalePreparationCode.protectsMemory=true := by
  have hq : Parts.literal (1/4)=⟨1,0,4⟩ := by norm_num [Parts.literal]
  simp only [scalePreparationCode,scalePrepareInitial,Control.prepend,List.foldr_cons,
    List.foldr_nil,Control.code,Instruction.code,hq]
  decide

theorem scalePreparation_protects_tables :
    ([5,6,7,8,9,37,200,202,203,204,205,210,212,213,214,215,216,220,221,222,223]:List ℕ).all
      (fun i => scalePreparationCode.protectsTape i)=true := by
  have hq : Parts.literal (1/4)=⟨1,0,4⟩ := by norm_num [Parts.literal]
  simp only [scalePreparationCode,scalePrepareInitial,Control.prepend,List.foldr_cons,
    List.foldr_nil,Control.code,Instruction.code,hq]
  decide

#print axioms scalePreparation_executes
#print axioms scalePreparation_protects_tables
end Maxwell.Continuum.Calibration.RawCutoff
