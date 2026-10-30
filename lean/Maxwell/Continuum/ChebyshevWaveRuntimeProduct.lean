import Maxwell.Continuum.ChebyshevWaveRuntimeSample
import Maxwell.Continuum.ChebyshevWaveProductLocalWidths
import Maxwell.Continuum.PhaseRuntimeFloorFrame

/-! The full Fourier summand is computed by fixed code, including exact
integer-floor reduction of its character phase. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow RationalTaylor
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

def evaluationWorkspace : Finset ℕ := Phase.Runtime.workspace ids∪DyadicFloor.workspace ids
def productCode : Code :=
  .seq sampleCode (.seq (DyadicFloor.code 0 2 5)
    (.seq (NatAssign.code (binaryStage .sub 5 5 2))
      (.seq (Phase.Runtime.loadedCode RationalTaylor.Runtime.cosineCycle 6 5 672 671)
        (.seq (Phase.Runtime.code RationalTaylor.Runtime.sineCycle 7 5) (program productInstructions)))))
def productWidth (Q P W B : ℕ) : ℕ := B+productInputWidth Q P W+2*Q+P+32
def productCost (Q P W B oldQ oldN : ℕ) : ℕ :=
  sampleCost Q P (sampleWidth Q P W B oldQ oldN)+
    DyadicFloor.costBound 0 (productWidth Q P W B)+stageCost (productWidth Q P W B)+
    (64*(productWidth Q P W B+1)+Phase.Runtime.costBound 1 P (productWidth Q P W B))+
    Phase.Runtime.costBound 1 P (productWidth Q P W B)+
    (6*operationCost (64*(productWidth Q P W B+1))+1)

theorem arithmetic_subset_evaluation : RationalDataflow.workspace ids⊆evaluationWorkspace := by
  intro i hi
  apply Finset.mem_union_left
  rcases Finset.mem_union.mp hi with hz|hr
  · exact Finset.mem_union_left _ hz
  · exact Finset.mem_union_right _ (Finset.mem_union_left _ hr)

theorem Parameters.floor_frame {Q P : ℕ} {S : Finset ℕ} {s t : Store} (h : Parameters Q P s)
    (f : BinaryPrecision.Frame (DyadicFloor.workspace S) s.val t.val) : Parameters Q P t := by
  intro i hi
  have hr := parameterIds_range i hi
  exact word_of_eq (f.tapes i (DyadicFloor.high_outside_workspace S i (by omega))) (h i hi)

theorem Parameters.character {Q P : ℕ} {s : Store} (h : Parameters Q P s) :
    Word s.val 672 1 ∧ Word s.val 671 P := by
  exact ⟨h.inner.1,by simpa [parameterValues_eq,scannedParameters,initialParameters] using h 671 (by decide)⟩

theorem product_executes (Q P W B oldQ oldN : ℕ) (v : ℕ→Parts) (hw : WidthBank ids B v)
    (h0 : (v 0).Width W) (h1 : (v 1).Width W) (h5 : (v 5).Width W) (hg : Good ids v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready ids v s)
    (hp : Phase.Runtime.Clean s.val) (hf : DyadicFloor.Clean s.val) (hm : Parameters Q P s)
    (hqo : Word s.val 652 oldQ) (hno : Word s.val 653 oldN) :
    ∃cost t,Executes input tape productCode cost s t ∧ cost≤productCost Q P W B oldQ oldN ∧
      Ready ids (productValues Q P v) t ∧ Phase.Runtime.Clean t.val ∧ DyadicFloor.Clean t.val ∧
      Parameters Q P t ∧ Word t.val 652 1 ∧ Word t.val 653 P ∧
      BinaryPrecision.Frame evaluationWorkspace s.val t.val := by
  let V := productWidth Q P W B
  have hV : 10≤V := by dsimp [V,productWidth];omega
  have hlocal : B+productInputWidth Q P W≤V := by dsimp [V,productWidth];omega
  have hPQ : (2*(Q+1)).bits.length≤V := (Machin.Runtime.nat_bits_le_self _).trans (by dsimp [V,productWidth];omega)
  have hPN : (P+4).bits.length≤V := (Machin.Runtime.nat_bits_le_self _).trans (by dsimp [V,productWidth];omega)
  have hP : P.bits.length≤V := (Machin.Runtime.nat_bits_le_self _).trans (by dsimp [V,productWidth];omega)
  have hone : (1:ℕ).bits.length≤V := by norm_num;omega
  have widths := product_states_width_local Q P W B v hw h0 h1 h5
  obtain ⟨c0,s0,e0,hc0,b0,z0,hm0,q0,n0,f0⟩ := sample_executes Q P W B oldQ oldN v hw h0 h1
    input tape s hs hp hm hqo hno
  have zf0 := hf.runtimePhase_frame f0
  have hx0 : (sampleValues Q P v 5).Valid := by
    simpa [sampleValues,state3,state2,state1] using hg 5 (by decide)
  obtain ⟨c1,s1,e1,hc1,b1,zf1,f1⟩ := DyadicFloor.executes ids 0 2 5 (by decide) (by decide)
    (sampleValues Q P v) V (widths.1.mono hlocal) hx0 input tape s0 b0 zf0
  have he1 : Function.update (sampleValues Q P v) 2 (DyadicFloor.result 0 (sampleValues Q P v 5))=
      state4 Q P v := by simp [state4,sampleValues,state3,state2,state1]
  rw [he1] at b1
  have z1 := DyadicFloor.runtimePhase_clean z0 f1 b1
  have hm1 := hm0.floor_frame f1
  have q1 := word_of_eq (f1.tapes 652 (DyadicFloor.high_outside_workspace ids 652 (by omega))) q0
  have n1 := word_of_eq (f1.tapes 653 (DyadicFloor.high_outside_workspace ids 653 (by omega))) n0
  obtain ⟨c2,s2,e2,hc2,b2,f2⟩ := binary_executes ids .sub 5 5 2 (by decide) (by decide) (by decide)
    (state4 Q P v) V (widths.2.1.mono hlocal) input tape s1 b1
  have he2 : Function.update (state4 Q P v) 5 (BinaryOp.sub.eval (state4 Q P v 5) (state4 Q P v 2))=
      state5 Q P v := by simp [state5,state4,reducedTurn,fractionalValue,BinaryOp.eval,sampleValues,state3,state2,state1]
  rw [he2] at b2
  have z2 := z1.arithmetic_frame f2 b2
  have zf2 := zf1.arithmetic_frame f2
  have hm2 := hm1.arithmetic_frame f2
  have q2 := word_of_eq (f2.tapes 652 (RationalDataflow.outside_workspace ids 652 (by omega))) q1
  have n2 := word_of_eq (f2.tapes 653 (RationalDataflow.outside_workspace ids 653 (by omega))) n1
  obtain ⟨c3,s3,e3,hc3,b3,z3,q3,n3,f3⟩ := Phase.Runtime.loaded_executes ids RationalTaylor.Runtime.cosineCycle
    1 P (2*(Q+1)) (P+4) 6 5 672 671 V (by decide) (by decide) (by decide) (by decide)
    (state5 Q P v) (widths.2.2.1.mono hlocal) hone hP hPQ hPN hV input tape s2 b2 z2 q2 n2
    hm2.character.1 hm2.character.2
  rw [RationalTaylor.Runtime.cosineCycle_signs] at b3
  have he3 : Function.update (state5 Q P v) 6 (Phase.result cosineSigns 1 P (state5 Q P v 5))=
      state6 Q P v := by simp [state6,state5,characterReal]
  rw [he3] at b3
  have zf3 := zf2.runtimePhase_frame f3
  have hm3 := hm2.phase_frame f3
  obtain ⟨c4,s4,e4,hc4,b4,z4,q4,n4,f4⟩ := Phase.Runtime.executes ids RationalTaylor.Runtime.sineCycle
    1 P 7 5 (by decide) (by decide) (state6 Q P v) V (widths.2.2.2.1.mono hlocal)
    hone hP hV input tape s3 b3 z3 q3 n3
  rw [RationalTaylor.Runtime.sineCycle_signs] at b4
  have he4 : Function.update (state6 Q P v) 7 (Phase.result sineSigns 1 P (state6 Q P v 5))=
      state7 Q P v := by simp [state7,state6,state5,characterImag]
  rw [he4] at b4
  have zf4 := zf3.runtimePhase_frame f4
  have hm4 := hm3.phase_frame f4
  have htrace := WidthTrace.mono ids productInstructions (state7 Q P v) _ (64*(V+1))
    (Nat.mul_le_mul_left 64 (Nat.add_le_add_right hlocal 1))
    (product_widthTrace_local Q P W B v hw h0 h1 h5)
  obtain ⟨c5,t,e5,hc5,b5,f5⟩ := program_executes ids productInstructions productInstructions_valid
    (state7 Q P v) (64*(V+1)) htrace input tape s4 b4
  change Ready ids (productValues Q P v) t at b5
  have hc5' : c5≤6*operationCost (64*(V+1))+1 := by
    simpa only [show productInstructions.length=6 by rfl] using hc5
  have qt := word_of_eq (f5.tapes 652 (RationalDataflow.outside_workspace ids 652 (by omega))) q4
  have nt := word_of_eq (f5.tapes 653 (RationalDataflow.outside_workspace ids 653 (by omega))) n4
  refine ⟨c0+(c1+(c2+(c3+(c4+c5)))),t,e0.seq (e1.seq (e2.seq (e3.seq (e4.seq e5)))),?_,
    b5,z4.arithmetic_frame f5 b5,zf4.arithmetic_frame f5,hm4.arithmetic_frame f5,qt,nt,?_⟩
  · unfold productCost
    change _≤sampleCost Q P (sampleWidth Q P W B oldQ oldN)+DyadicFloor.costBound 0 V+stageCost V+
      (64*(V+1)+Phase.Runtime.costBound 1 P V)+Phase.Runtime.costBound 1 P V+(6*operationCost (64*(V+1))+1)
    omega
  · exact (f0.mono Finset.subset_union_left).trans
      ((f1.mono Finset.subset_union_right).trans
        ((f2.mono arithmetic_subset_evaluation).trans
          ((f3.mono Finset.subset_union_left).trans
            ((f4.mono Finset.subset_union_left).trans (f5.mono arithmetic_subset_evaluation)))))

#print axioms product_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime
