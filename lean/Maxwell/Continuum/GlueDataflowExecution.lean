import Maxwell.Continuum.GlueDataflowFinish

/-! The fixed signed glue call executes from, and returns to, an ordinary
rational dataflow bank with its precision word intact. -/
namespace Maxwell.Continuum.RationalDataflow.Glue
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def costBound (N W : ℕ) : ℕ :=
  stageCost W+300*(2*W+4)+2+stageCost (W+1)+GlueMachine.Runtime.costBound N (W+1)+
    (6*(GlueMachine.order N).bits.length+4)+(2+stageCost (workWidth N W))+stageCost (workWidth N W)

theorem seeded_outside (N : ℕ) (v : ℕ→Parts) (source i : ℕ)
    (hi : i∉GlueMachine.Runtime.ids) : seeded N v source i=dataValues v i := by
  by_cases hs : i<1000
  · rw [seeded_small N v source i hs,dataValues_small v hs]
    have h600 : i≠600 := by intro he;subst i;exact hi (by decide)
    have h601 : i≠601 := by intro he;subst i;exact hi (by decide)
    have h640 : i≠640 := by intro he;subst i;exact hi (by decide)
    simp only [GlueMachine.Runtime.initialValues,GlueMachine.initialValues,h600,h601,h640,ite_false]
  · exact seeded_large N v source i (by omega)

theorem clearCounter_executes (S : Finset ℕ) (v : ℕ→ℕ)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (word : List Bool)
    (hb : NatAssign.Bank ((allIds S).erase 641) v s.val) (hz : NatAssign.Scratch s.val)
    (hw : BankArray.Word s.val 641 word) :
    ∃ t,Executes input tape (.call (TapeOps.clear 641)) (6*word.length+4) s t ∧
      NatAssign.Bank (allIds S) (Function.update v 641 0) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame (workspace S) s.val t.val := by
  obtain ⟨origin,hw⟩ := hw
  obtain ⟨t,ex,ht,ft⟩ := WordCall.clear 641 input tape word origin s hw
  have he (i : ℕ) (hi : i≠641) : t.val.tapes i=s.val.tapes i := by simp only [ht,Function.update_of_ne hi]
  refine ⟨t,ex,?_,?_,⟨ft.1,ft.2.1,ft.2.2.1,ft.2.2.2.1,ft.2.2.2.2.1,?_⟩⟩
  · intro i hi
    by_cases hh : i=641
    · subst i
      simp only [Function.update_self]
      apply (zero_word_iff_blank _ _).mpr
      exact ⟨origin+word.length,by simp [ht]⟩
    · simpa only [Function.update_of_ne hh] using word_of_eq (he i hh) (hb i (Finset.mem_erase.mpr ⟨hh,hi⟩))
  · intro i hi;exact blank_of_eq (he i (by omega)) (hz i hi)
  · intro i hi
    apply he
    intro hh;subst i
    exact hi (Finset.mem_union_right _ (Finset.mem_union_right _ (by decide)))

theorem correct_executes (S : Finset ℕ) (N : ℕ) (v : ℕ→Parts) (source W : ℕ)
    (hs : source∈S) (hw : WidthBank S W v) (hN : N.bits.length≤W) (hW : 4≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hb : NatAssign.Bank (allIds S) (unsignedFinished N v source) s.val)
    (hz : NatAssign.Scratch s.val)
    (hsg : s.val.registers 200=decide ((v source).positive<(v source).negative)) :
    ∃ cost t,Executes input tape
      (.branch 200 (NatAssign.code GlueMachine.writeZero) .skip) cost s t ∧
      cost≤2+stageCost (workWidth N W) ∧ NatAssign.Bank (allIds S) (corrected N v source) t.val ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame (workspace S) s.val t.val := by
  by_cases hn : (v source).positive<(v source).negative
  · have hv : ∀a∈GlueMachine.writeZero,a.Valid (allIds S) := by
      simp [GlueMachine.writeZero,NatAssign.Instruction.Valid,allIds,GlueMachine.Runtime.ids,
        GlueMachine.ids,GlueMachine.extra,SelectedParameters.Compare.ids,RationalTaylor.ids]
    obtain ⟨cost,t,ex,hc,bt,zt,ft⟩ := stage_executes S GlueMachine.writeZero hv (by simp [GlueMachine.writeZero])
      (unsignedFinished N v source) (workWidth N W) (unsignedFinished_width S N v source W hs hw hN hW)
      (by
        have hpow : 1≤(N+W+9)^4 := one_le_pow₀ (by omega)
        simp [GlueMachine.writeZero,NatAssign.Instruction.literalWidth,workWidth]
        omega) input tape s hb hz
    refine ⟨1+cost,t,Executes.yes (by simpa only [hn,decide_true] using hsg) ex,by omega,?_,zt,ft⟩
    simpa only [corrected,ite_eq_left hn] using bt
  · refine ⟨2,s,Executes.no (by simpa only [hn,decide_false] using hsg) (Executes.skip s),
      by omega,?_,hz,BinaryPrecision.Frame.refl _ _⟩
    simpa only [corrected,ite_eq_right hn] using hb

theorem executes (S : Finset ℕ) (N target source : ℕ) (ht : target∈S) (hs' : source∈S)
    (v : ℕ→Parts) (W : ℕ) (hw : WidthBank S W v) (hN : N.bits.length≤W) (hW : 4≤W)
    (hx : (v source).Valid) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : Ready S v s) (hz : Clean s.val) (hp : Word s.val 640 N) :
    ∃ cost t,Executes input tape (code target source) cost s t ∧ cost≤costBound N W ∧
      Ready S (Function.update v target (result N (v source))) t ∧ Clean t.val ∧
      Word t.val 640 N ∧ BinaryPrecision.Frame (workspace S) s.val t.val := by
  obtain ⟨c0,s0,e0,h0,b0,z0,f0⟩ := stage_executes S (prepareInverse source)
    (prepare_valid S source hs') (by simp [prepareInverse]) (initialValues N v) W
    (initial_width S N v W hw hN) (by simp [prepareInverse,NatAssign.Instruction.literalWidth])
    input tape s (initial_bank S N v s hs hz hp) hs.2
  rw [prepare_values] at b0
  have hmag : RationalMagnitude.ids⊆allIds S := (magnitude_subset S).trans Finset.subset_union_left
  have hin0 : Function.update (beforeInverse v source) 640 N 30=(v source).positive := by
    simpa only [Function.update_of_ne (by decide : (30:ℕ)≠640)] using (beforeInverse_inputs v source).1
  have hin1 : Function.update (beforeInverse v source) 640 N 31=(v source).negative := by
    simpa only [Function.update_of_ne (by decide : (31:ℕ)≠640)] using (beforeInverse_inputs v source).2.1
  have hin2 : Function.update (beforeInverse v source) 640 N 34=0 := by
    simpa only [Function.update_of_ne (by decide : (34:ℕ)≠640)] using (beforeInverse_inputs v source).2.2
  obtain ⟨c1,s1,e1,h1,b1,z1,f1,sg⟩ := RationalMagnitude.executes (allIds S) hmag (allIds_ge S)
    (Function.update (beforeInverse v source) 640 N) hin2 input tape s0 b0 z0
  have b1' : NatAssign.Bank (allIds S) (Function.update (afterInverseMagnitude v source) 640 N) s1.val := by
    simpa only [hin0,hin1,afterInverseMagnitude,
      Function.update_comm (by decide : (34:ℕ)≠640)] using b1
  have hc1 : c1≤300*(2*W+4) := by
    rw [hin0,hin1] at h1
    exact h1.trans (Nat.mul_le_mul_left 300 (by
      have hpos := (hw source hs').1
      have hneg := (hw source hs').2.1
      omega))
  have hsg : s1.val.registers 23=decide ((v source).positive<(v source).negative) := by
    simpa only [hin0,hin1,magnitude_sign] using sg
  let s2 := Store.ofState (s1.val.setRegister 200 (s1.val.registers 23 && s1.val.registers 23))
  have e2 := Executes.bitAnd input tape s1 200 23 23
  have hsg2 : s2.val.registers 200=decide ((v source).positive<(v source).negative) := by
    simp only [s2,Store.ofState,BitRAMState.setRegister,Function.update_self,Bool.and_self,hsg]
  have b2 : NatAssign.Bank (allIds S) (Function.update (afterInverseMagnitude v source) 640 N) s2.val := b1'
  have z2 : NatAssign.Scratch s2.val := z1
  have f2 : BinaryPrecision.Frame (workspace S) s1.val s2.val := ⟨rfl,rfl,rfl,rfl,rfl,fun _ _ => rfl⟩
  obtain ⟨c3,s3,e3,h3,b3,z3,f3⟩ := stage_executes S (prepareCall source)
    (prepareCall_valid S source hs') (by simp [prepareCall,clearMagnitude])
    (Function.update (afterInverseMagnitude v source) 640 N) (W+1)
    (afterMagnitude_width S N v source W hs' hw hN)
    (by simp [prepareCall,clearMagnitude,NatAssign.Instruction.literalWidth]) input tape s2 b2 z2
  change NatAssign.Bank (allIds S) (seeded N v source) s3.val at b3
  have coreSeed : NatAssign.Bank GlueMachine.Runtime.ids
      (GlueMachine.Runtime.initialValues (Phase.magnitude (v source)) (v source).denominator N) s3.val := by
    intro i hi
    have hh := b3 i (Finset.mem_union_right _ hi)
    rwa [seeded_small N v source i (ids_small i hi)] at hh
  have hm : (Phase.magnitude (v source)).bits.length≤W+1 :=
    (IntegerNormSquare.magnitude_bits_length_le _ _).trans
      (Nat.add_le_add_right (max_le (hw source hs').1 (hw source hs').2.1) 1)
  obtain ⟨c4,s4,word,e4,h4,b4,z4,w4,hl,_,_,_,f4⟩ := GlueMachine.Runtime.core_executes
    (Phase.magnitude (v source)) (v source).denominator N (W+1) hm
    ((hw source hs').2.2.trans (by omega)) (hN.trans (by omega)) (by omega) hx input tape s3 coreSeed z3
  have returnedBank : NatAssign.Bank ((allIds S).erase 641) (returned N v source) s4.val := by
    intro i hi
    obtain ⟨hne,hi⟩ := Finset.mem_erase.mp hi
    by_cases hh : i∈GlueMachine.Runtime.ids
    · simpa only [returned,ite_eq_left hh] using b4 i (Finset.mem_erase.mpr ⟨hne,hh⟩)
    · have ho : i∉GlueMachine.Runtime.workspace := by
        have hg := allIds_ge S i hi
        simp only [GlueMachine.Runtime.workspace,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
        exact not_or_intro (by omega) hh
      simpa only [returned,ite_eq_right hh,seeded_outside N v source i hh]
        using word_of_eq (f4.tapes i ho) (b3 i hi)
  obtain ⟨s5,e5,b5,z5,f5⟩ := clearCounter_executes S (returned N v source) input tape s4 word returnedBank z4 w4
  have hsg5 : s5.val.registers 200=decide ((v source).positive<(v source).negative) :=
    (e5.protectsRegister 200 (by rfl)).trans ((e4.protectsRegister 200 core_protects_sign).trans
      ((e3.protectsRegister 200 (by rfl)).trans hsg2))
  obtain ⟨c6,s6,e6,h6,b6,z6,f6⟩ := correct_executes S N v source W hs' hw hN hW input tape s5 b5 z5 hsg5
  obtain ⟨c7,t,e7,h7,b7,z7,f7⟩ := stage_executes S (finishCall target)
    (finishCall_valid S target ht) (by simp [finishCall,copyOutput,NatAssign.clearList_length,privateTapes])
    (corrected N v source) (workWidth N W) (corrected_width S N v source W hs' hw hN hW)
    (by
      intro a ha
      rcases List.mem_append.mp ha with hc|hz'
      · simp only [copyOutput,List.mem_cons,List.not_mem_nil,or_false] at hc
        rcases hc with rfl|rfl|rfl <;> simp [NatAssign.Instruction.literalWidth]
      · rw [NatAssign.clearList_literalWidth privateTapes a hz'];omega)
    input tape s6 b6 z6
  rw [finishCall_values] at b7
  refine ⟨c0+(c1+(2+(c3+(c4+((6*word.length+4)+(c6+c7)))))),t,
    e0.seq (e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq e7)))))),?_,?_,?_,?_,
    f0.trans ((f1.mono ?_).trans (f2.trans (f3.trans ((f4.mono ?_).trans (f5.trans (f6.trans f7))))))⟩
  · unfold costBound;omega
  · refine ⟨?_,z7⟩
    intro i hi
    have hne : i≠640 := fun h => precision_outside S (h ▸ hi)
    simpa only [initialValues,Function.update_of_ne hne] using b7 i (Finset.mem_union_left _ hi)
  · intro i hi
    obtain ⟨hne,hi⟩ := Finset.mem_erase.mp hi
    have hh := b7 i (Finset.mem_union_right _ hi)
    rw [initialValues,Function.update_of_ne hne,dataValues_small _ (ids_small i hi)] at hh
    exact (zero_word_iff_blank _ _).mp hh
  · simpa only [initialValues,Function.update_self] using b7 640 (Finset.mem_union_right _ (by decide))
  · intro i hi
    rcases Finset.mem_union.mp hi with hz'|hm'
    · exact Finset.mem_union_left _ hz'
    · exact Finset.mem_union_right _ (hmag hm')
  · intro i hi
    rcases Finset.mem_union.mp hi with hz'|ht'
    · exact Finset.mem_union_left _ hz'
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ ht')

#print axioms executes
end Maxwell.Continuum.RationalDataflow.Glue
