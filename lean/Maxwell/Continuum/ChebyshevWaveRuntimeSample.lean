import Maxwell.Continuum.ChebyshevWaveRuntimeParameters

/-! A single fixed nested-wave sampler. Numeric ranges, precision, frequency,
and sample location are all read from stored words. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow RationalTaylor
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def sampleCode : Code :=
  .seq (Phase.Runtime.loadedCode RationalTaylor.Runtime.cosineCycle 2 1 672 675)
    (.seq (NatAssign.code (binaryStage .mul 2 0 2))
      (.seq (Phase.Runtime.loadedCode RationalTaylor.Runtime.cosineCycle 3 2 673 674)
        (Phase.Runtime.code RationalTaylor.Runtime.sineCycle 4 2)))
def sampleWidth (Q P W B oldQ oldN : ℕ) : ℕ :=
  B+WaveMachine.workWidth Q P W+(2*Q+P+12)+oldQ.bits.length+oldN.bits.length+10
def sampleCost (Q P V : ℕ) : ℕ :=
  (64*(V+1)+Phase.Runtime.costBound 1 (Calibration.phaseBits Q (P+4)) V)+stageCost V+
    (64*(V+1)+Phase.Runtime.costBound (2*(Q+1)) (P+4) V)+
    Phase.Runtime.costBound (2*(Q+1)) (P+4) V

theorem sample_executes (Q P W B oldQ oldN : ℕ) (v : ℕ→Parts)
    (hw : WidthBank ids B v) (h0 : (v 0).Width W) (h1 : (v 1).Width W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready ids v s)
    (hz : Phase.Runtime.Clean s.val) (hp : Parameters Q P s)
    (hqo : Word s.val 652 oldQ) (hno : Word s.val 653 oldN) :
    ∃cost t,Executes input tape sampleCode cost s t ∧
      cost≤sampleCost Q P (sampleWidth Q P W B oldQ oldN) ∧
      Ready ids (sampleValues Q P v) t ∧ Phase.Runtime.Clean t.val ∧ Parameters Q P t ∧
      Word t.val 652 (2*(Q+1)) ∧ Word t.val 653 (P+4) ∧
      BinaryPrecision.Frame (Phase.Runtime.workspace ids) s.val t.val := by
  let V := sampleWidth Q P W B oldQ oldN
  have hV : 10≤V := by dsimp [V,sampleWidth];omega
  have hlocal : B+WaveMachine.workWidth Q P W≤V := by dsimp [V,sampleWidth];omega
  have hmeta : 2*Q+P+12≤V := by dsimp [V,sampleWidth];omega
  have hqoW : oldQ.bits.length≤V := by dsimp [V,sampleWidth];omega
  have hnoW : oldN.bits.length≤V := by dsimp [V,sampleWidth];omega
  have hinner : (Calibration.phaseBits Q (P+4)).bits.length≤V := by
    have h := parameterValues_width Q P 675
    simp only [parameterValues_eq,show (675:ℕ)≠672 by decide,show (675:ℕ)≠673 by decide,
      show (675:ℕ)≠674 by decide,ite_false,ite_true] at h
    exact h.trans hmeta
  have houterQ : (2*(Q+1)).bits.length≤V := by
    have h := parameterValues_width Q P 673
    simp only [parameterValues_eq,show (673:ℕ)≠672 by decide,ite_false,ite_true] at h
    exact h.trans hmeta
  have houterN : (P+4).bits.length≤V := by
    have h := parameterValues_width Q P 674
    simp only [parameterValues_eq,show (674:ℕ)≠672 by decide,show (674:ℕ)≠673 by decide,
      ite_false,ite_true] at h
    exact h.trans hmeta
  have hone : (1:ℕ).bits.length≤V := by norm_num;omega
  have widths := states_width_local Q P W B v hw h0 h1
  obtain ⟨c0,s0,e0,hc0,b0,z0,q0,n0,f0⟩ := Phase.Runtime.loaded_executes ids RationalTaylor.Runtime.cosineCycle
    1 (Calibration.phaseBits Q (P+4)) oldQ oldN 2 1 672 675 V (by decide) (by decide)
    (by decide) (by decide) v (widths.1.mono hlocal) hone hinner hqoW hnoW hV
    input tape s hs hz hqo hno hp.inner.1 hp.inner.2
  rw [RationalTaylor.Runtime.cosineCycle_signs] at b0
  change Ready ids (state1 Q P v) s0 at b0
  have hp0 := hp.phase_frame f0
  obtain ⟨c1,s1,e1,hc1,b1,f1⟩ := binary_executes ids .mul 2 0 2 (by decide) (by decide) (by decide)
    (state1 Q P v) V (widths.2.1.mono hlocal) input tape s0 b0
  have he1 : Function.update (state1 Q P v) 2 (BinaryOp.mul.eval (state1 Q P v 0) (state1 Q P v 2))=
      state2 Q P v := by simp [state1,state2,argumentValue,BinaryOp.eval]
  rw [he1] at b1
  have z1 := z0.arithmetic_frame f1 b1
  have hp1 := hp0.arithmetic_frame f1
  have q1 := word_of_eq (f1.tapes 652 (RationalDataflow.outside_workspace ids 652 (by omega))) q0
  have n1 := word_of_eq (f1.tapes 653 (RationalDataflow.outside_workspace ids 653 (by omega))) n0
  obtain ⟨c2,s2,e2,hc2,b2,z2,q2,n2,f2⟩ := Phase.Runtime.loaded_executes ids RationalTaylor.Runtime.cosineCycle
    (2*(Q+1)) (P+4) 1 (Calibration.phaseBits Q (P+4)) 3 2 673 674 V (by decide) (by decide)
    (by decide) (by decide) (state2 Q P v) (widths.2.2.1.mono hlocal)
    houterQ houterN hone hinner hV input tape s1 b1 z1 q1 n1 hp1.outer.1 hp1.outer.2
  rw [RationalTaylor.Runtime.cosineCycle_signs] at b2
  have he2 : Function.update (state2 Q P v) 3 (Phase.result cosineSigns (2*(Q+1)) (P+4) (state2 Q P v 2))=
      state3 Q P v := by simp only [state3,realValue,state2,Function.update_self]
  rw [he2] at b2
  have hp2 := hp1.phase_frame f2
  obtain ⟨c3,t,e3,hc3,b3,z3,q3,n3,f3⟩ := Phase.Runtime.executes ids RationalTaylor.Runtime.sineCycle
    (2*(Q+1)) (P+4) 4 2 (by decide) (by decide) (state3 Q P v) V
    (widths.2.2.2.1.mono hlocal) houterQ houterN hV input tape s2 b2 z2 q2 n2
  rw [RationalTaylor.Runtime.sineCycle_signs] at b3
  have he3 : Function.update (state3 Q P v) 4 (Phase.result sineSigns (2*(Q+1)) (P+4) (state3 Q P v 2))=
      sampleValues Q P v := by simp [sampleValues,imagValue,state3,state2]
  rw [he3] at b3
  refine ⟨c0+(c1+(c2+c3)),t,e0.seq (e1.seq (e2.seq e3)),?_,b3,z3,hp2.phase_frame f3,q3,n3,
    f0.trans ((f1.mono ?_).trans (f2.trans f3))⟩
  · unfold sampleCost
    change _≤(64*(V+1)+Phase.Runtime.costBound 1 (Calibration.phaseBits Q (P+4)) V)+stageCost V+
      (64*(V+1)+Phase.Runtime.costBound (2*(Q+1)) (P+4) V)+Phase.Runtime.costBound (2*(Q+1)) (P+4) V
    omega
  · intro i hi
    rcases Finset.mem_union.mp hi with hz'|hr
    · exact Finset.mem_union_left _ hz'
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hr)

#print axioms sample_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime
