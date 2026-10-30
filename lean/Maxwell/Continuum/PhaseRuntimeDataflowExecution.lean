import Maxwell.Continuum.PhaseRuntimeDataflowFinish
import Maxwell.Cost.Structured.RegisterFootprint

/-! Actual repeated shared-bank calls to the fixed runtime phase program. -/
namespace Maxwell.Continuum.RationalDataflow.Phase.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def costBound (Q N W : ℕ) : ℕ :=
  stageCost W+300*(2*W+4)+2+stageCost (W+1)+
    PhaseMachine.Runtime.costBound Q N (W+1)+stageCost (workWidth Q N W)

theorem executes (S : Finset ℕ) (base : RationalTaylor.Runtime.Cycle) (Q N target source : ℕ)
    (ht : target∈S) (hs' : source∈S) (v : ℕ→Parts) (W : ℕ) (hw : WidthBank S W v)
    (hQ : Q.bits.length≤W) (hN : N.bits.length≤W) (hW : 10≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready S v s)
    (hz : Clean s.val) (hq : Word s.val 652 Q) (hn : Word s.val 653 N) :
    ∃cost t,Executes input tape (code base target source) cost s t ∧ cost≤costBound Q N W ∧
      Ready S (Function.update v target (Phase.result (RationalTaylor.Runtime.cycleSigns base) Q N (v source))) t ∧
      Clean t.val ∧ Word t.val 652 Q ∧ Word t.val 653 N ∧ BinaryPrecision.Frame (workspace S) s.val t.val := by
  obtain ⟨c0,s0,e0,h0,b0,z0,f0⟩ := stage_executes S (prepareInverse source)
    (prepare_valid S source hs') (by simp [prepareInverse]) (initialValues Q N v) W
    (initial_width S Q N v W hw hQ hN) (by simp [prepareInverse,NatAssign.Instruction.literalWidth])
    input tape s (initial_bank S Q N v s hs hz hq hn) hs.2
  rw [prepare_values] at b0
  have hmag : RationalMagnitude.ids⊆allIds S := (magnitude_subset S).trans Finset.subset_union_left
  have hin0 : parameters Q N (beforeInverse v source) 30=(v source).positive := by
    simpa only [parameters,Function.update_of_ne (by decide : (30:ℕ)≠653),
      Function.update_of_ne (by decide : (30:ℕ)≠652)] using (beforeInverse_inputs v source).1
  have hin1 : parameters Q N (beforeInverse v source) 31=(v source).negative := by
    simpa only [parameters,Function.update_of_ne (by decide : (31:ℕ)≠653),
      Function.update_of_ne (by decide : (31:ℕ)≠652)] using (beforeInverse_inputs v source).2.1
  have hin2 : parameters Q N (beforeInverse v source) 34=0 := by
    simpa only [parameters,Function.update_of_ne (by decide : (34:ℕ)≠653),
      Function.update_of_ne (by decide : (34:ℕ)≠652)] using (beforeInverse_inputs v source).2.2
  obtain ⟨c1,s1,e1,h1,b1,z1,f1,sg⟩ := RationalMagnitude.executes (allIds S) hmag (allIds_ge S)
    (parameters Q N (beforeInverse v source)) hin2 input tape s0 b0 z0
  rw [hin0,hin1] at b1
  have b1' : NatAssign.Bank (allIds S) (parameters Q N (afterInverseMagnitude v source)) s1.val := by
    simpa only [afterInverseMagnitude,parameters,
      Function.update_comm (by decide : (34:ℕ)≠653),Function.update_comm (by decide : (34:ℕ)≠652)] using b1
  have hc1 : c1≤300*(2*W+4) := by
    rw [hin0,hin1] at h1
    exact h1.trans (Nat.mul_le_mul_left 300 (by
      have hpos := (hw source hs').1
      have hneg := (hw source hs').2.1
      omega))
  have hsg : s1.val.registers 23=Phase.negative (v source) := by
    simpa only [hin0,hin1,magnitude_sign,Phase.negative] using sg
  let s2 := Store.ofState (s1.val.setRegister 200 (s1.val.registers 23 && s1.val.registers 23))
  have e2 := Executes.bitAnd input tape s1 200 23 23
  have hsg2 : s2.val.registers 200=Phase.negative (v source) := by
    simp only [s2,Store.ofState,BitRAMState.setRegister,Function.update_self,Bool.and_self,hsg]
  have b2 : NatAssign.Bank (allIds S) (parameters Q N (afterInverseMagnitude v source)) s2.val := b1'
  have z2 : NatAssign.Scratch s2.val := z1
  have f2 : BinaryPrecision.Frame (workspace S) s1.val s2.val := ⟨rfl,rfl,rfl,rfl,rfl,fun _ _ => rfl⟩
  obtain ⟨c3,s3,e3,h3,b3,z3,f3⟩ := stage_executes S (prepareCall source)
    (prepareCall_valid S source hs') (by simp [prepareCall,clearMagnitude])
    (parameters Q N (afterInverseMagnitude v source)) (W+1)
    (afterMagnitude_width S Q N v source W hs' hw hQ hN)
    (by simp [prepareCall,clearMagnitude,NatAssign.Instruction.literalWidth]) input tape s2 b2 z2
  change NatAssign.Bank (allIds S) (seeded Q N v source) s3.val at b3
  have hsg3 : s3.val.registers 200=Phase.negative (v source) :=
    (e3.protectsRegister 200 (by rfl)).trans hsg2
  have coreSeed : NatAssign.Bank PhaseMachine.Runtime.ids
      (PhaseMachine.Runtime.initialValues (Phase.magnitude (v source)) (v source).denominator Q N) s3.val := by
    intro i hi
    have hh := b3 i (Finset.mem_union_right _ hi)
    rwa [seeded_small Q N v source i (ids_small i hi)] at hh
  have hm : (Phase.magnitude (v source)).bits.length≤W+1 :=
    (IntegerNormSquare.magnitude_bits_length_le _ _).trans
      (Nat.add_le_add_right (max_le (hw source hs').1 (hw source hs').2.1) 1)
  obtain ⟨c4,s4,e4,h4,b4,z4,f4⟩ := PhaseMachine.Runtime.executes (Phase.negative (v source)) base
    (Phase.magnitude (v source)) (v source).denominator Q N (W+1) hm
    ((hw source hs').2.2.trans (by omega)) (hQ.trans (by omega)) (hN.trans (by omega)) (by omega)
    input tape s3 coreSeed z3 hsg3
  have returnedBank : NatAssign.Bank (allIds S) (returned base Q N v source) s4.val := by
    intro i hi
    by_cases hh : i∈PhaseMachine.Runtime.ids
    · simpa only [returned,ite_eq_left hh] using b4 i hh
    · have ho : i∉PhaseMachine.Runtime.workspace := by
        have hg := allIds_ge S i hi
        simp only [PhaseMachine.Runtime.workspace,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
        exact not_or_intro (by omega) hh
      simpa only [returned,ite_eq_right hh,seeded_outside Q N v source i hh] using
        word_of_eq (f4.tapes i ho) (b3 i hi)
  obtain ⟨c5,t,e5,h5,b5,z5,f5⟩ := stage_executes S (finishCall target)
    (finishCall_valid S target ht)
    (by simp [finishCall,Phase.copyOutput,NatAssign.clearList_length,privateTapes,Phase.privateTapes])
    (returned base Q N v source) (workWidth Q N W) (returned_width S base Q N v source W hs' hw hQ hN)
    (fun a ha => by rw [finishCall_literalWidth target a ha];omega) input tape s4 returnedBank z4
  rw [finishCall_values] at b5
  obtain ⟨ready,clean,qword,nword⟩ := returned_ready S Q N _ t b5 z5
  refine ⟨c0+(c1+(2+(c3+(c4+c5)))),t,e0.seq (e1.seq (e2.seq (e3.seq (e4.seq e5)))),?_,
    ready,clean,qword,nword,f0.trans ((f1.mono ?_).trans (f2.trans (f3.trans ((f4.mono ?_).trans f5))))⟩
  · unfold costBound
    omega
  · intro i hi
    rcases Finset.mem_union.mp hi with hz'|hm'
    · exact Finset.mem_union_left _ hz'
    · exact Finset.mem_union_right _ (hmag hm')
  · intro i hi
    rcases Finset.mem_union.mp hi with hz'|ht'
    · exact Finset.mem_union_left _ hz'
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ ht')

#print axioms executes
end Maxwell.Continuum.RationalDataflow.Phase.Runtime
