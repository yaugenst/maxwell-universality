import Maxwell.Continuum.CalibrationRootProduct

/-! Runtime execution of an actual root-grid Fourier summand.  The fixed
instruction stream calls glue, cosine, sine, and the two exact products. -/
namespace Maxwell.Continuum.RationalDataflow.RootProduct
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalTaylor
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

def workWidth (N W : ℕ) : ℕ := coefficientWidth N W+W+10
def workspace (S : Finset ℕ) : Finset ℕ := Glue.workspace S∪Phase.Runtime.workspace S
def costBound (N W : ℕ) : ℕ := RootSample.costBound N W+
  2*Phase.Runtime.costBound 1 N (workWidth N W)+2*operationCost (4*(workWidth N W+1))+1

theorem coordinate_mem (i : Fin 3) : i.val∈inputs := by
  have hi := i.isLt
  simp only [inputs,Finset.mem_insert,Finset.mem_singleton]
  omega

theorem workWidth_ge (N W : ℕ) : W≤workWidth N W := by unfold workWidth;omega

theorem argumentWidth_le (N W : ℕ) : 6*W+10≤workWidth N W := by
  have hp : N+6*W+20≤(N+6*W+20)^4 := Nat.le_self_pow (by decide) _
  unfold workWidth coefficientWidth
  omega

theorem root_width_le (N W : ℕ) : 2^28*(N+6*W+19)^4≤workWidth N W := by
  have hp := Nat.pow_le_pow_left (by omega : N+6*W+19≤N+6*W+20) 4
  unfold workWidth coefficientWidth
  nlinarith only [hp,Nat.zero_le ((N+6*W+20)^4)]

theorem phase_width_le (N W : ℕ) : 2^68*(1+N+W+12)^4≤workWidth N W := by
  have hp := Nat.pow_le_pow_left (by omega : 1+N+W+12≤N+6*W+20) 4
  unfold workWidth coefficientWidth
  nlinarith only [hp,Nat.zero_le ((N+6*W+20)^4)]

theorem root_bank_width (S : Finset ℕ) (hS : inputs⊆S) (N W : ℕ) (v : ℕ→Parts)
    (hw : WidthBank S W v) : WidthBank S (workWidth N W) (RootSample.values N v) := by
  have hy (i : Fin 3) : (RootSample.coordinates v i).Width W := hw i (hS (coordinate_mem i))
  intro i hi
  by_cases h4 : i=4
  · subst i
    exact (RootSample.values_width N W v hy).mono (root_width_le N W)
  by_cases h3 : i=3
  · subst i
    rw [RootSample.values,Function.update_of_ne (by decide : (3:ℕ)≠4),RootSample.argument_output]
    exact (RootSample.rawArgument_width _ W hy).mono (argumentWidth_le N W)
  rw [RootSample.values_unchanged N v i ⟨h3,h4⟩]
  exact (hw i hi).mono (workWidth_ge N W)

theorem afterCos_width (S : Finset ℕ) (hS : inputs⊆S) (N W : ℕ) (v : ℕ→Parts)
    (hw : WidthBank S W v) : WidthBank S (workWidth N W) (afterCos N v) := by
  exact (root_bank_width S hS N W v hw).update 6
    ((Phase.result_width cosineSigns 1 N W (v 5) (hw 5 (hS (by decide)))).mono (phase_width_le N W))

theorem afterSin_width (S : Finset ℕ) (hS : inputs⊆S) (N W : ℕ) (v : ℕ→Parts)
    (hw : WidthBank S W v) : WidthBank S (workWidth N W) (afterSin N v) := by
  exact (afterCos_width S hS N W v hw).update 7
    ((Phase.result_width sineSigns 1 N W (v 5) (hw 5 (hS (by decide)))).mono (phase_width_le N W))

theorem executes (S : Finset ℕ) (hS : inputs⊆S) (N W : ℕ) (v : ℕ→Parts)
    (hw : WidthBank S W v) (hg : Good S v) (hN : N.bits.length≤W) (hW : 10≤W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : Ready S v s) (hz : Glue.Clean s.val) (hzp : Phase.Runtime.Clean s.val)
    (hp : Word s.val 640 N) (hq : Word s.val 652 1) (hn : Word s.val 653 N) :
    ∃ cost t,Executes input tape code cost s t ∧ cost≤costBound N W ∧
      Ready S (values N v) t ∧ Good S (values N v) ∧
      Glue.Clean t.val ∧ Phase.Runtime.Clean t.val ∧
      Word t.val 640 N ∧ Word t.val 652 1 ∧ Word t.val 653 N ∧
      BinaryPrecision.Frame (workspace S) s.val t.val := by
  have hroot : RootSample.inputs⊆S := root_inputs.trans hS
  obtain ⟨c0,s0,e0,h0,b0,z0,p0,f0,g0,_⟩ := RootSample.executes S hroot N W v hw hg hN
    (by omega) input tape s hs hz hp
  have zp0 := RootSample.phase_clean_glue hzp f0 b0 z0
  have q0 := word_of_eq (f0.tapes 652 (RootSample.glue_parameter_outside S 652 (Or.inl rfl))) hq
  have n0 := word_of_eq (f0.tapes 653 (RootSample.glue_parameter_outside S 653 (Or.inr rfl))) hn
  have hWU := workWidth_ge N W
  have h1 : (1:ℕ).bits.length≤workWidth N W := by change 1≤_;omega
  obtain ⟨c1,s1,e1,hc1,b1,zp1,q1,n1,f1⟩ := Phase.Runtime.executes S Runtime.cosineCycle 1 N 6 5
    (hS (by decide)) (hS (by decide)) (RootSample.values N v) (workWidth N W)
    (root_bank_width S hS N W v hw) h1 (hN.trans hWU) (hW.trans hWU) input tape s0 b0 zp0 q0 n0
  have b1' : Ready S (afterCos N v) s1 := by
    simpa only [Runtime.cosineCycle_signs,RootSample.values_unchanged N v 5 (by decide),afterCos,cosine] using b1
  have g1 : Good S (afterCos N v) := g0.update 6 (Phase.result_valid _ 1 N (v 5) (hg 5 (hS (by decide))))
  have z1 := RootSample.glue_clean_phase z0 f1 b1' zp1
  have p1 := word_of_eq (f1.tapes 640 (RootSample.phase_glue_precision_outside S)) p0
  obtain ⟨c2,s2,e2,hc2,b2,zp2,q2,n2,f2⟩ := Phase.Runtime.executes S Runtime.sineCycle 1 N 7 5
    (hS (by decide)) (hS (by decide)) (afterCos N v) (workWidth N W)
    (afterCos_width S hS N W v hw) h1 (hN.trans hWU) (hW.trans hWU) input tape s1 b1' zp1 q1 n1
  have b2' : Ready S (afterSin N v) s2 := by
    simpa only [Runtime.sineCycle_signs,afterCos,Function.update_of_ne (by decide : (5:ℕ)≠6),
      RootSample.values_unchanged N v 5 (by decide),afterSin,sine] using b2
  have g2 : Good S (afterSin N v) := g1.update 7 (Phase.result_valid _ 1 N (v 5) (hg 5 (hS (by decide))))
  have z2 := RootSample.glue_clean_phase z1 f2 b2' zp2
  have p2 := word_of_eq (f2.tapes 640 (RootSample.phase_glue_precision_outside S)) p1
  have ht : multiply.WidthTrace S (4*(workWidth N W+1)) (afterSin N v) := by
    simpa only [multiply_steps,show 2^2=4 by rfl] using multiply.automatic_widthTrace S (multiply_valid S hS)
      (afterSin N v) (workWidth N W) (afterSin_width S hS N W v hw) (multiply_literals _)
  obtain ⟨c3,t,e3,hc3,b3,f3⟩ := multiply.executes S (multiply_valid S hS) (afterSin N v)
    (4*(workWidth N W+1)) ht g2 (multiply_admissible _) input tape s2 b2'
  have p3 := word_of_eq (f3.tapes 640 (by
    simp only [RationalDataflow.workspace,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    exact not_or_intro (by omega) (Glue.precision_outside S))) p2
  have q3 := word_of_eq (f3.tapes 652 (Phase.Runtime.parameter_outside_workspace S 652 (Or.inl rfl))) q2
  have n3 := word_of_eq (f3.tapes 653 (Phase.Runtime.parameter_outside_workspace S 653 (Or.inr rfl))) n2
  refine ⟨c0+(c1+(c2+c3)),t,e0.seq (e1.seq (e2.seq e3)),?_,b3,
    multiply.evaluate_good S (multiply_valid S hS) _ g2 (multiply_admissible _),
    RootSample.glue_clean_arithmetic z2 f3 b3,Phase.Runtime.Clean.arithmetic_frame zp2 f3 b3,
    p3,q3,n3,?_⟩
  · simp only [multiply_steps] at hc3
    unfold costBound
    omega
  · apply (f0.mono Finset.subset_union_left).trans
      ((f1.mono Finset.subset_union_right).trans ((f2.mono Finset.subset_union_right).trans (f3.mono ?_)))
    intro i hi
    apply Finset.mem_union_left
    rcases Finset.mem_union.mp hi with hi|hi
    · exact Finset.mem_union_left _ hi
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hi)

#print axioms executes
end Maxwell.Continuum.RationalDataflow.RootProduct
