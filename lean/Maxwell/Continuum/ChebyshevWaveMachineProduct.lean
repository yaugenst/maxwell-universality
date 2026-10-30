import Maxwell.Continuum.ChebyshevWaveMachineProductWidths

/-! Complete runtime evaluation of an actual finite Fourier summand,
including signed modular reduction and both complex multiplications. -/
namespace Maxwell.Continuum.Profile.WaveMachine
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow RationalTaylor
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192

def evaluationWorkspace : Finset ℕ := Phase.workspace ids∪DyadicFloor.workspace ids
def productCode (Q P : ℕ) : Code :=
  .seq (sampleCode Q P)
    (.seq (DyadicFloor.code 0 2 5)
      (.seq (NatAssign.code (binaryStage .sub 5 5 2))
        (.seq (Phase.code cosineSigns 1 P 6 5)
          (.seq (Phase.code sineSigns 1 P 7 5) (program productInstructions)))))
def productCost (Q P W : ℕ) : ℕ :=
  sampleCost Q P W+DyadicFloor.costBound 0 (productInputWidth Q P W)+
    stageCost (productInputWidth Q P W)+2*Phase.costBound 1 P (productInputWidth Q P W)+
      (6*operationCost (productWorkWidth Q P W)+1)

theorem arithmetic_subset_evaluation : RationalDataflow.workspace ids⊆evaluationWorkspace := by
  intro i hi
  apply Finset.mem_union_left
  rcases Finset.mem_union.mp hi with hz|hr
  · exact Finset.mem_union_left _ hz
  · exact Finset.mem_union_right _ (Finset.mem_union_left _ hr)

theorem product_executes (Q P W : ℕ) (v : ℕ→Parts) (hw : WidthBank ids W v) (hg : Good ids v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready ids v s)
    (hp : Phase.Clean s.val) (hf : DyadicFloor.Clean s.val) :
    ∃ cost t,Executes input tape (productCode Q P) cost s t ∧ cost≤productCost Q P W ∧
      Ready ids (productValues Q P v) t ∧ Phase.Clean t.val ∧ DyadicFloor.Clean t.val ∧
      BinaryPrecision.Frame evaluationWorkspace s.val t.val := by
  have hw' := product_states_width Q P W v hw
  obtain ⟨c0,s0,e0,h0,b0,z0,f0⟩ := sample_executes Q P W v hw input tape s hs hp
  have zf0 := hf.phase_frame f0
  have hx0 : (sampleValues Q P v 5).Valid := by
    simpa [sampleValues,state3,state2,state1] using hg 5 (by decide)
  obtain ⟨c1,s1,e1,h1,b1,zf1,f1⟩ := DyadicFloor.executes ids 0 2 5 (by decide) (by decide)
    (sampleValues Q P v) (productInputWidth Q P W) hw'.1 hx0 input tape s0 b0 zf0
  have he1 : Function.update (sampleValues Q P v) 2 (DyadicFloor.result 0 (sampleValues Q P v 5))=
      state4 Q P v := by simp [state4,sampleValues,state3,state2,state1]
  rw [he1] at b1
  have z1 := DyadicFloor.phase_clean z0 f1 b1
  obtain ⟨c2,s2,e2,h2,b2,f2⟩ := binary_executes ids .sub 5 5 2 (by decide) (by decide) (by decide)
    (state4 Q P v) (productInputWidth Q P W) hw'.2.1 input tape s1 b1
  have he2 : Function.update (state4 Q P v) 5 (BinaryOp.sub.eval (state4 Q P v 5) (state4 Q P v 2))=
      state5 Q P v := by simp [state5,state4,reducedTurn,fractionalValue,BinaryOp.eval,sampleValues,state3,state2,state1]
  rw [he2] at b2
  have z2 := z1.arithmetic_frame f2 b2
  have zf2 := zf1.arithmetic_frame f2
  obtain ⟨c3,s3,e3,h3,b3,z3,f3⟩ := Phase.executes ids cosineSigns 1 P 6 5 (by decide) (by decide)
    (state5 Q P v) (productInputWidth Q P W) hw'.2.2.1 input tape s2 b2 z2
  have he3 : Function.update (state5 Q P v) 6 (Phase.result cosineSigns 1 P (state5 Q P v 5))=
      state6 Q P v := by simp [state6,state5,characterReal]
  rw [he3] at b3
  have zf3 := zf2.phase_frame f3
  obtain ⟨c4,s4,e4,h4,b4,z4,f4⟩ := Phase.executes ids sineSigns 1 P 7 5 (by decide) (by decide)
    (state6 Q P v) (productInputWidth Q P W) hw'.2.2.2.1 input tape s3 b3 z3
  have he4 : Function.update (state6 Q P v) 7 (Phase.result sineSigns 1 P (state6 Q P v 5))=
      state7 Q P v := by simp [state7,state6,state5,characterImag]
  rw [he4] at b4
  have zf4 := zf3.phase_frame f4
  obtain ⟨c5,t,e5,h5,b5,f5⟩ := program_executes ids productInstructions productInstructions_valid
    (state7 Q P v) (productWorkWidth Q P W) (product_widthTrace Q P W v hw) input tape s4 b4
  change Ready ids (productValues Q P v) t at b5
  have hc5 : c5≤6*operationCost (productWorkWidth Q P W)+1 := by
    simpa only [show productInstructions.length=6 by rfl] using h5
  refine ⟨c0+(c1+(c2+(c3+(c4+c5)))),t,e0.seq (e1.seq (e2.seq (e3.seq (e4.seq e5)))),?_,
    b5,z4.arithmetic_frame f5 b5,zf4.arithmetic_frame f5,?_⟩
  · unfold productCost
    omega
  · exact (f0.mono Finset.subset_union_left).trans
      ((f1.mono Finset.subset_union_right).trans
        ((f2.mono arithmetic_subset_evaluation).trans
          ((f3.mono Finset.subset_union_left).trans
            ((f4.mono Finset.subset_union_left).trans (f5.mono arithmetic_subset_evaluation)))))

theorem product_computes (grid : ℕ) [NeZero grid] (Q P W : ℕ) (j : ZMod grid) (n : ℤ)
    (v : ℕ→Parts) (hw : WidthBank ids W v) (hg : Good ids v)
    (hgrid : (v 1).value=Calibration.gridTurn grid j)
    (hturn : (v 5).value= -(j.val:ℚ)*(n:ℚ)/grid)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready ids v s)
    (hp : Phase.Clean s.val) (hf : DyadicFloor.Clean s.val) :
    ∃ t, (runPriced ((productCode Q P).compile.next input tape) (productCost Q P W+1) s.val).finished=
      some (t.place (productCode Q P).size) ∧
      (runPriced ((productCode Q P).compile.next input tape) (productCost Q P W+1) s.val).instructions≤productCost Q P W ∧
      Ready ids (productValues Q P v) t ∧ Phase.Clean t.val ∧ DyadicFloor.Clean t.val ∧
      (productValues Q P v 0).value=(waveProductSample grid (v 0).value Q P n j).re.center ∧
      (productValues Q P v 1).value=(waveProductSample grid (v 0).value Q P n j).im.center := by
  obtain ⟨cost,t,he,hc,hr,hp',hf',_⟩ := product_executes Q P W v hw hg input tape s hs hp hf
  have hout := he.compiled_run (productCost Q P W+1) (by omega)
  exact ⟨t,hout.1,hout.2 ▸ hc,hr,hp',hf',productValues_correct grid Q P j n v hg hgrid hturn⟩

#print axioms product_executes
#print axioms product_computes
end Maxwell.Continuum.Profile.WaveMachine
