import Maxwell.Continuum.ChebyshevWaveMachineData

/-! Nested elementary evaluation for an actual finite-grid wave sample.
No sampled-value oracle or execution trace is supplied by the caller. -/
namespace Maxwell.Continuum.Profile.WaveMachine
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow RationalTaylor
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def sampleCode (Q P : ℕ) : Code :=
  .seq (Phase.code cosineSigns 1 (Calibration.phaseBits Q (P+4)) 2 1)
    (.seq (NatAssign.code (binaryStage .mul 2 0 2))
      (.seq (Phase.code cosineSigns (2*(Q+1)) (P+4) 3 2)
        (Phase.code sineSigns (2*(Q+1)) (P+4) 4 2)))
def sampleCost (Q P W : ℕ) : ℕ :=
  Phase.costBound 1 (Calibration.phaseBits Q (P+4)) (workWidth Q P W)+
    stageCost (workWidth Q P W)+2*Phase.costBound (2*(Q+1)) (P+4) (workWidth Q P W)

theorem sample_executes (Q P W : ℕ) (v : ℕ→Parts) (hw : WidthBank ids W v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready ids v s) (hz : Phase.Clean s.val) :
    ∃ cost t,Executes input tape (sampleCode Q P) cost s t ∧ cost≤sampleCost Q P W ∧
      Ready ids (sampleValues Q P v) t ∧ Phase.Clean t.val ∧
      BinaryPrecision.Frame (Phase.workspace ids) s.val t.val := by
  have hw' := states_width Q P W v hw
  obtain ⟨c0,s0,e0,h0,b0,z0,f0⟩ := Phase.executes ids cosineSigns 1 (Calibration.phaseBits Q (P+4))
    2 1 (by decide) (by decide) v (workWidth Q P W) hw'.1 input tape s hs hz
  change Ready ids (state1 Q P v) s0 at b0
  obtain ⟨c1,s1,e1,h1,b1,f1⟩ := binary_executes ids .mul 2 0 2 (by decide) (by decide) (by decide)
    (state1 Q P v) (workWidth Q P W) hw'.2.1 input tape s0 b0
  have he1 : Function.update (state1 Q P v) 2 (BinaryOp.mul.eval (state1 Q P v 0) (state1 Q P v 2))=
      state2 Q P v := by simp [state1,state2,argumentValue,BinaryOp.eval]
  rw [he1] at b1
  have z1 := z0.arithmetic_frame f1 b1
  obtain ⟨c2,s2,e2,h2,b2,z2,f2⟩ := Phase.executes ids cosineSigns (2*(Q+1)) (P+4)
    3 2 (by decide) (by decide) (state2 Q P v) (workWidth Q P W) hw'.2.2.1 input tape s1 b1 z1
  have he2 : Function.update (state2 Q P v) 3 (Phase.result cosineSigns (2*(Q+1)) (P+4) (state2 Q P v 2))=
      state3 Q P v := by simp only [state3,realValue,state2,Function.update_self]
  rw [he2] at b2
  obtain ⟨c3,t,e3,h3,b3,z3,f3⟩ := Phase.executes ids sineSigns (2*(Q+1)) (P+4)
    4 2 (by decide) (by decide) (state3 Q P v) (workWidth Q P W) hw'.2.2.2.1 input tape s2 b2 z2
  have he3 : Function.update (state3 Q P v) 4 (Phase.result sineSigns (2*(Q+1)) (P+4) (state3 Q P v 2))=
      sampleValues Q P v := by simp [sampleValues,imagValue,state3,state2]
  rw [he3] at b3
  refine ⟨c0+(c1+(c2+c3)),t,e0.seq (e1.seq (e2.seq e3)),?_,b3,z3,
    f0.trans ((f1.mono ?_).trans (f2.trans f3))⟩
  · unfold sampleCost
    omega
  · intro i hi
    rcases Finset.mem_union.mp hi with hz'|hr
    · exact Finset.mem_union_left _ hz'
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ hr)

theorem sample_computes (Q P W : ℕ) (v : ℕ→Parts) (hw : WidthBank ids W v) (hg : Good ids v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready ids v s) (hz : Phase.Clean s.val) :
    ∃ t, (runPriced ((sampleCode Q P).compile.next input tape) (sampleCost Q P W+1) s.val).finished=
      some (t.place (sampleCode Q P).size) ∧
      (runPriced ((sampleCode Q P).compile.next input tape) (sampleCost Q P W+1) s.val).instructions≤sampleCost Q P W ∧
      Ready ids (sampleValues Q P v) t ∧ Phase.Clean t.val ∧
      (sampleValues Q P v 3).value=(waveSample (v 0).value Q P (v 1).value).re.center ∧
      (sampleValues Q P v 4).value=(waveSample (v 0).value Q P (v 1).value).im.center := by
  obtain ⟨cost,t,he,hc,hr,hz',_⟩ := sample_executes Q P W v hw input tape s hs hz
  have hout := he.compiled_run (sampleCost Q P W+1) (by omega)
  exact ⟨t,hout.1,hout.2 ▸ hc,hr,hz',sampleValues_correct Q P v hg⟩

#print axioms sample_executes
#print axioms sample_computes
end Maxwell.Continuum.Profile.WaveMachine
