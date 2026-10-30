import Maxwell.Continuum.PhaseDataflowFinish
import Maxwell.Cost.Structured.RegisterFootprint

/-! An actual shared-bank phase call, including transfer and cleanup.
The same finite program can be called repeatedly inside cached array loops. -/
namespace Maxwell.Continuum.RationalDataflow.Phase
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

def sharedStageCost (B : ℕ) : ℕ := 2^160*(B+2)^2
def costBound (Q N W : ℕ) : ℕ :=
  sharedStageCost W+300*(2*W+4)+2+sharedStageCost (W+1)+
    (PhaseMachine.fullCost Q N (W+1)+1)+sharedStageCost (workWidth Q N W)

theorem stage_executes (S : Finset ℕ) (ins : List NatAssign.Instruction)
    (hv : ∀a∈ins,a.Valid (allIds S)) (hl : ins.length≤40)
    (v : ℕ→ℕ) (B : ℕ) (hw : ∀i∈allIds S,(v i).bits.length≤B)
    (hc : ∀a∈ins,a.literalWidth≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank (allIds S) v s.val) (hsc : NatAssign.Scratch s.val) :
    ∃ cost t,Executes input tape (NatAssign.code ins) cost s t ∧ cost≤sharedStageCost B ∧
      NatAssign.Bank (allIds S) (NatAssign.values ins v) t.val ∧ NatAssign.Scratch t.val ∧
      BinaryPrecision.Frame (workspace S) s.val t.val := by
  obtain ⟨cost,t,he,hcost,hb,hsc',hf⟩ := NatAssign.executes (allIds S) (allIds_ge S) ins hv v input tape s hs hsc
  have hp := NatAssign.price_bound (allIds S) ins hv v B hw hc
  have hcoef : 3000*8^ins.length≤(2:ℕ)^160 := by
    calc
      _ ≤ 3000*8^40 := Nat.mul_le_mul_left 3000 (Nat.pow_le_pow_right (by decide) hl)
      _ ≤ _ := by norm_num
  refine ⟨cost,t,he,hcost.trans (hp.trans (Nat.mul_le_mul_right _ hcoef)),hb,hsc',hf.mono ?_⟩
  intro i hi
  rcases Finset.mem_union.mp hi with hz|ht
  · exact Finset.mem_union_left _ hz
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
    apply Finset.mem_union_right
    have h := hv a ha
    cases a <;> first | exact h | exact h.2.1

theorem seeded_eq_outside (v : ℕ→Parts) (source i : ℕ) (hi : i∉PhaseMachine.allIds) :
    seeded v source i=dataValues v i := by
  by_cases hs : i<1000
  · rw [seeded_small v source i hs,dataValues_small v hs]
    have h630 : i≠630 := by intro h;subst i;exact hi (by decide)
    have h631 : i≠631 := by intro h;subst i;exact hi (by decide)
    simp only [PhaseMachine.initialValues,ite_eq_right h630,ite_eq_right h631]
  · exact seeded_large v source i (by omega)

theorem executes (S : Finset ℕ) (base : ℕ→Sign) (Q N target source : ℕ)
    (ht : target∈S) (hs' : source∈S) (v : ℕ→Parts) (W : ℕ) (hw : WidthBank S W v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : RationalDataflow.Ready S v s)
    (hz : Clean s.val) :
    ∃ cost t,Executes input tape (code base Q N target source) cost s t ∧ cost≤costBound Q N W ∧
      RationalDataflow.Ready S (Function.update v target (result base Q N (v source))) t ∧
      Clean t.val ∧ BinaryPrecision.Frame (workspace S) s.val t.val := by
  obtain ⟨c0,s0,e0,h0,b0,z0,f0⟩ := stage_executes S (prepareInverse source)
    (prepare_valid S source hs') (by simp [prepareInverse]) (dataValues v) W
    (initial_width S v W hw) (by simp [prepareInverse,NatAssign.Instruction.literalWidth])
    input tape s (initial_bank S v s hs hz) hs.2
  rw [prepareInverse_values] at b0
  have hmag : RationalMagnitude.ids⊆allIds S :=
    (magnitude_subset S).trans Finset.subset_union_left
  obtain ⟨c1,s1,e1,h1,b1,z1,f1,sg⟩ := RationalMagnitude.executes (allIds S) hmag
    (allIds_ge S) (beforeInverse v source) (beforeInverse_inputs v source).2.2 input tape s0 b0 z0
  have b1' : NatAssign.Bank (allIds S) (afterInverseMagnitude v source) s1.val := by
    simpa only [afterInverseMagnitude,(beforeInverse_inputs v source).1,(beforeInverse_inputs v source).2.1] using b1
  have hc1 : c1≤300*(2*W+4) := by
    rw [(beforeInverse_inputs v source).1,(beforeInverse_inputs v source).2.1] at h1
    exact h1.trans (Nat.mul_le_mul_left 300 (by
      have hp := (hw source hs').1
      have hn := (hw source hs').2.1
      omega))
  have hsg : s1.val.registers 23=negative (v source) := by
    simpa only [(beforeInverse_inputs v source).1,(beforeInverse_inputs v source).2.1,
      magnitude_sign,negative] using sg
  let s2 := Store.ofState (s1.val.setRegister 200 (s1.val.registers 23 && s1.val.registers 23))
  have e2 := Executes.bitAnd input tape s1 200 23 23
  have hsg2 : s2.val.registers 200=negative (v source) := by
    simp only [s2,Store.ofState,BitRAMState.setRegister,Function.update_self,Bool.and_self,hsg]
  have b2 : NatAssign.Bank (allIds S) (afterInverseMagnitude v source) s2.val := b1'
  have z2 : NatAssign.Scratch s2.val := z1
  have f2 : BinaryPrecision.Frame (workspace S) s1.val s2.val :=
    ⟨rfl,rfl,rfl,rfl,rfl,fun _ _ => rfl⟩
  obtain ⟨c3,s3,e3,h3,b3,z3,f3⟩ := stage_executes S (prepareCall source)
    (prepareCall_valid S source hs') (by simp [prepareCall,clearMagnitude])
    (afterInverseMagnitude v source) (W+1) (afterMagnitude_width S v source W hs' hw)
    (by simp [prepareCall,clearMagnitude,NatAssign.Instruction.literalWidth]) input tape s2 b2 z2
  change NatAssign.Bank (allIds S) (seeded v source) s3.val at b3
  have phaseSeed : NatAssign.Bank PhaseMachine.allIds
      (PhaseMachine.initialValues (magnitude (v source)) (v source).denominator) s3.val := by
    intro i hi
    have h := b3 i (Finset.mem_union_right _ hi)
    rwa [seeded_small v source i (PhaseMachine.allIds_small i hi)] at h
  have hsg3 : s3.val.registers 200=negative (v source) := by
    exact (e3.protectsRegister 200 (by rfl)).trans hsg2
  have hm : (magnitude (v source)).bits.length≤W+1 :=
    (IntegerNormSquare.magnitude_bits_length_le _ _).trans
      (Nat.add_le_add_right (max_le (hw source hs').1 (hw source hs').2.1) 1)
  have hd : (v source).denominator.bits.length≤W+1 := (hw source hs').2.2.trans (Nat.le_succ W)
  obtain ⟨c4,s4,e4,h4,b4,z4,f4⟩ := PhaseMachine.executes_bank (negative (v source)) base
    (magnitude (v source)) (v source).denominator Q N (W+1) hm hd input tape s3 phaseSeed z3 hsg3
  have returnedBank : NatAssign.Bank (allIds S) (returned base Q N v source) s4.val := by
    intro i hi
    by_cases hp : i∈PhaseMachine.allIds
    · simpa only [returned,ite_eq_left hp] using b4 i hp
    · have ho : i∉PhaseMachine.allWorkspace := by
        have hg := allIds_ge S i hi
        simp only [PhaseMachine.allWorkspace,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
        exact not_or_intro (by omega) hp
      have h := word_of_eq (f4.tapes i ho) (b3 i hi)
      simpa only [returned,ite_eq_right hp,seeded_eq_outside v source i hp] using h
  obtain ⟨c5,t,e5,h5,b5,z5,f5⟩ := stage_executes S (finishCall target)
    (finishCall_valid S target ht) (by simp [finishCall,copyOutput,NatAssign.clearList_length,privateTapes])
    (returned base Q N v source) (workWidth Q N W) (returned_width S base Q N v source W hs' hw)
    (fun a ha => by rw [finishCall_literalWidth target a ha];omega) input tape s4 returnedBank z4
  rw [finishCall_values] at b5
  refine ⟨c0+(c1+(2+(c3+(c4+c5)))),t,e0.seq (e1.seq (e2.seq (e3.seq (e4.seq e5)))),?_,
    ⟨fun i hi => b5 i (Finset.mem_union_left _ hi),z5⟩,clean_of_bank S _ t.val b5,?_⟩
  · unfold costBound
    omega
  · apply f0.trans
    apply (f1.mono ?_).trans (f2.trans (f3.trans ((f4.mono ?_).trans f5)))
    · intro i hi
      rcases Finset.mem_union.mp hi with hz|hm
      · exact Finset.mem_union_left _ hz
      · exact Finset.mem_union_right _ (hmag hm)
    · intro i hi
      rcases Finset.mem_union.mp hi with hz|hp
      · exact Finset.mem_union_left _ hz
      · exact Finset.mem_union_right _ (Finset.mem_union_right _ hp)

#print axioms executes
end Maxwell.Continuum.RationalDataflow.Phase
