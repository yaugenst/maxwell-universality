import Maxwell.Continuum.GlueMachineStages
import Maxwell.Continuum.RationalTaylorFraction

/-! Executable cutoff-branch and reciprocal-exponential evaluation of `glueApprox`. -/

namespace Maxwell.Continuum.GlueMachine
open Maxwell.Certificate Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096
attribute [local irreducible] Elementary.expApprox

def resultWidth (N W : ℕ) : ℕ := RationalTaylor.width (order N) (preparedWidth N W)+1
def comparisonCost (N W : ℕ) : ℕ := 2^25*(seedWidth N W+2)^2
def costBound (N W : ℕ) : ℕ :=
  2*stageCost N W+comparisonCost N W+RationalTaylor.costBound (order N) (preparedWidth N W)+2

def expCode (N : ℕ) : Code :=
  .seq (NatAssign.code prepareExp) (RationalTaylor.program negativeSigns (order N))
def core (N : ℕ) : Code :=
  .seq (NatAssign.code (initializeStage N))
    (.seq (SelectedParameters.Compare.code 608 609 600 601)
      (.branch 35 (expCode N) (NatAssign.code writeZero)))
def program (signRegister N : ℕ) : Code := .branch signRegister (NatAssign.code writeZero) (core N)

def Output (q : ℚ) (B : ℕ) (s : Store) : Prop :=
  ∃ p n d : ℕ, Word s.val 602 p ∧ Word s.val 603 n ∧ Word s.val 604 d ∧ 0<d ∧
    q=((p:ℚ)-n)/d ∧ p.bits.length≤B ∧ n.bits.length≤B ∧ d.bits.length≤B

theorem zero_executes (N W : ℕ) (v : ℕ→ℕ)
    (hw : ∀ i∈ids, (v i).bits.length≤seedWidth N W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids v s.val) (hsc : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape (NatAssign.code writeZero) cost s t ∧ cost≤stageCost N W ∧
      Output 0 (resultWidth N W) t ∧ NatAssign.Scratch t.val ∧ BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨cost,t,he,hc,hb,hz,hf⟩ := stage_executes N W writeZero (stages_valid N).2.2
    (by decide) (by simp [writeZero,NatAssign.Instruction.literalWidth]; unfold seedWidth; omega)
    v hw input tape s hs hsc
  refine ⟨cost,t,he,hc,?_,hz,hf⟩
  refine ⟨0,0,1,?_,?_,?_,by decide,by norm_num,?_,?_,?_⟩
  · simpa [writeZero,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value] using hb 602 (by decide)
  · simpa [writeZero,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value] using hb 603 (by decide)
  · simpa [writeZero,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value] using hb 604 (by decide)
  · simp
  · simp
  · have h : (1:ℕ).bits.length=1 := by decide
    rw [h]
    unfold resultWidth
    omega

theorem exp_executes (a b N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W) (ha0 : 0<a)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids (comparedValues a b N) s.val) (hsc : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape (expCode N) cost s t ∧
      cost≤stageCost N W+RationalTaylor.costBound (order N) (preparedWidth N W) ∧
      Output (Elementary.expApprox (-((b:ℚ)/a)) (N+1) N).center (resultWidth N W) t ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨c0,s0,e0,h0,b0,z0,f0⟩ := stage_executes N W prepareExp (stages_valid N).2.1
    (by decide) (by simp [prepareExp,NatAssign.Instruction.literalWidth]) (comparedValues a b N)
    (fun i _ => compared_width a b N W ha hb i) input tape s hs hsc
  change NatAssign.Bank ids (preparedValues a b N) s0.val at b0
  have hsub : RationalTaylor.ids⊆ids := by decide
  obtain ⟨c1,t,e1,h1,ht,f1⟩ := RationalTaylor.program_executes (preparedValues a b N) negativeSigns
    (order N) (preparedWidth N W) (by unfold preparedWidth; omega)
    (fun i hi => prepared_width a b N W ha hb i (hsub hi)) input tape s0
    (fun i hi => b0 i (hsub hi)) z0
  have ht' : Ready b a negativeSigns (order N) t := by
    simpa only [(prepared_inputs a b N).1,(prepared_inputs a b N).2] using ht
  have hW : W≤preparedWidth N W := by unfold preparedWidth seedWidth; omega
  have hp := numerator_bits b a (fun k => (negativeSigns k).positive) (order N) (preparedWidth N W)
    (hb.trans hW) (ha.trans hW) (order N) le_rfl
  have hn := numerator_bits b a (fun k => (negativeSigns k).negative) (order N) (preparedWidth N W)
    (hb.trans hW) (ha.trans hW) (order N) le_rfl
  have hd := denominator_bits a (order N) (order N) (preparedWidth N W) le_rfl (ha.trans hW)
  refine ⟨c0+c1,t,e0.seq e1,Nat.add_le_add h0 h1,?_,ht.scratch,f0.trans (f1.mono (by decide))⟩
  refine ⟨_,_,_,?_,?_,?_,denominator_pos ha0 _,negative_expApprox_center b a ha0 (N+1) N,?_,?_,?_⟩
  · simpa [values,order] using ht'.bank 602 (by decide)
  · simpa [values,order] using ht'.bank 603 (by decide)
  · simpa [values,order] using ht'.bank 604 (by decide)
  · exact hp.trans (Nat.le_succ _)
  · exact hn.trans (Nat.le_succ _)
  · exact hd.trans (Nat.le_succ _)

theorem core_executes (a b N W : ℕ) (ha : a.bits.length≤W) (hb : b.bits.length≤W) (hb0 : 0<b)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids (initialValues a b) s.val) (hsc : NatAssign.Scratch s.val) :
    ∃ cost t, Executes input tape (core N) cost s t ∧ cost+1≤costBound N W ∧
      Output (Profile.glueApprox ((a:ℚ)/b) N).center (resultWidth N W) t ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨c0,s0,e0,h0,b0,z0,f0⟩ := stage_executes N W (initializeStage N) (stages_valid N).1
    (by simp [initializeStage]) (by
      simp [initializeStage,NatAssign.Instruction.literalWidth]
      have hn := nat_bits_le_self (N+1)
      have h1 : (1:ℕ).bits.length=1 := by decide
      unfold seedWidth
      omega) (initialValues a b) (fun i _ => initial_width a b N W ha hb i) input tape s hs hsc
  rw [initialize_values] at b0
  obtain ⟨c1,s1,e1,h1,sg1,b1,z1,f1⟩ := SelectedParameters.Compare.executes extra extra_ge 608 609 600 601
    (by decide) (by decide) (by decide) (by decide) (initializedValues a b N) (seedWidth N W)
    (fun i _ => initialized_width a b N W ha hb i)
    (by simp [initializedValues]) (by simpa [initializedValues,initialValues] using hb0)
    (by simp [initializedValues,initialValues]) (by simp [initializedValues,initialValues]) input tape s0 b0 z0
  change NatAssign.Bank ids (comparedValues a b N) s1.val at b1
  have h1' : c1≤comparisonCost N W := by
    unfold comparisonCost
    nlinarith only [h1]
  have sg : s1.val.registers 35=decide ((1:ℚ)/((N:ℚ)+1)<(a:ℚ)/b) := by
    simpa [initializedValues,initialValues] using sg1
  have frame01 : BinaryPrecision.Frame workspace s.val s1.val := f0.trans (f1.mono (by decide))
  by_cases hsmall : (a:ℚ)/b≤1/((N:ℚ)+1)
  · obtain ⟨c2,t,e2,h2,ho,z2,f2⟩ := zero_executes N W (comparedValues a b N)
      (fun i _ => compared_width a b N W ha hb i) input tape s1 b1 z1
    have hfalse : s1.val.registers 35=false := by rw [sg]; exact decide_eq_false (not_lt.mpr hsmall)
    refine ⟨c0+(c1+(1+c2)),t,e0.seq (e1.seq (Executes.no hfalse e2)),?_,?_,z2,frame01.trans f2⟩
    · unfold costBound
      omega
    · simpa only [Profile.glueApprox,ite_eq_left hsmall] using ho
  · have hqpos : (0:ℚ)<(a:ℚ)/b := lt_trans (by positivity : (0:ℚ)<1/((N:ℚ)+1)) (lt_of_not_ge hsmall)
    have ha0 : 0<a := by
      have h := (div_pos_iff_of_pos_right (show (0:ℚ)<b by exact_mod_cast hb0)).mp hqpos
      exact_mod_cast h
    obtain ⟨c2,t,e2,h2,ho,z2,f2⟩ := exp_executes a b N W ha hb ha0 input tape s1 b1 z1
    have htrue : s1.val.registers 35=true := by rw [sg]; exact decide_eq_true (lt_of_not_ge hsmall)
    refine ⟨c0+(c1+(1+c2)),t,e0.seq (e1.seq (Executes.yes htrue e2)),?_,?_,z2,frame01.trans f2⟩
    · unfold costBound
      omega
    · have he : (-1:ℚ)/((a:ℚ)/b)=-((b:ℚ)/a) := by simp only [neg_div,one_div,inv_div]
      simpa only [Profile.glueApprox,ite_eq_right hsmall,he] using ho

theorem executes (negative : Bool) (signRegister a b N W : ℕ)
    (ha : a.bits.length≤W) (hb : b.bits.length≤W) (hb0 : 0<b)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids (initialValues a b) s.val) (hsc : NatAssign.Scratch s.val)
    (hsg : s.val.registers signRegister=negative) :
    ∃ cost t, Executes input tape (program signRegister N) cost s t ∧ cost≤costBound N W ∧
      Output (Profile.glueApprox (signedFraction negative a b) N).center (resultWidth N W) t ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame workspace s.val t.val := by
  cases negative with
  | false =>
    obtain ⟨cost,t,he,hc,ho,hz,hf⟩ := core_executes a b N W ha hb hb0 input tape s hs hsc
    exact ⟨1+cost,t,Executes.no hsg he,by omega,ho,hz,hf⟩
  | true =>
    obtain ⟨cost,t,he,hc,ho,hz,hf⟩ := zero_executes N W (initialValues a b)
      (fun i _ => initial_width a b N W ha hb i) input tape s hs hsc
    have hsmall : -((a:ℚ)/b)≤1/((N:ℚ)+1) := le_trans (neg_nonpos.mpr (by positivity)) (by positivity)
    refine ⟨1+cost,t,Executes.yes hsg he,?_,?_,hz,hf⟩
    · unfold costBound
      omega
    · simpa only [signedFraction,ite_true,Profile.glueApprox,ite_eq_left hsmall] using ho

theorem compiled_computes (negative : Bool) (signRegister a b N W : ℕ)
    (ha : a.bits.length≤W) (hb : b.bits.length≤W) (hb0 : 0<b)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : NatAssign.Bank ids (initialValues a b) s.val) (hsc : NatAssign.Scratch s.val)
    (hsg : s.val.registers signRegister=negative) :
    ∃ (cost : ℕ) (t : Store),
      (runPriced ((program signRegister N).compile.next input tape) (costBound N W+1) s.val).finished=
        some (t.place (program signRegister N).size) ∧
      (runPriced ((program signRegister N).compile.next input tape) (costBound N W+1) s.val).instructions=cost ∧
      cost≤costBound N W ∧
      Output (Profile.glueApprox (signedFraction negative a b) N).center (resultWidth N W) t := by
  obtain ⟨cost,t,he,hc,ho,_,_⟩ := executes negative signRegister a b N W ha hb hb0 input tape s hs hsc hsg
  obtain ⟨hrun,hcost⟩ := he.compiled_run (costBound N W+1) (by omega)
  exact ⟨cost,t,hrun,hcost,hc,ho⟩

#print axioms core_executes
#print axioms compiled_computes

end Maxwell.Continuum.GlueMachine
