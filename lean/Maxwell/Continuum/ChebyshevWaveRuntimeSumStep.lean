import Maxwell.Continuum.ChebyshevWaveRuntimeProduct
import Maxwell.Continuum.ChebyshevWaveSumWords

/-! Fixed preparation, evaluation, and accumulation of one Fourier sample. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow RationalTaylor
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def sumStepCode : Code := .seq (program prepareInstructions) (.seq productCode (program accumulateInstructions))
def sumStepCost (Q P W B oldQ oldN : ℕ) : ℕ :=
  (4*operationCost (64*(B+1))+1)+productCost Q P (5*(W+1)) (B+5*(W+1)) oldQ oldN+
    (3*operationCost (64*(B+productWorkWidth Q P (5*(W+1))+1))+1)

theorem prepare_program_width (B : ℕ) : programWidth prepareInstructions (fun _ => B)≤64*(B+1) := by
  simp [prepareInstructions,programWidth,RationalDataflow.Instruction.widthUpdate,RationalDataflow.Instruction.resultWidth]
  omega

theorem accumulate_program_width (B : ℕ) : programWidth accumulateInstructions (fun _ => B)≤64*(B+1) := by
  simp [accumulateInstructions,programWidth,RationalDataflow.Instruction.widthUpdate,RationalDataflow.Instruction.resultWidth]
  omega

theorem prepared_bank_local (W B : ℕ) (v : ℕ→Parts) (hw : WidthBank ids B v)
    (hm : ∀i,10 ≤ i → i<16 → (v i).Width W) : WidthBank ids (B+5*(W+1)) (prepared v) := by
  have hp := prepared_operands_width W v hm
  intro i hi
  by_cases h0 : i=0
  · subst i;exact hp.1.mono (by omega)
  by_cases h1 : i=1
  · subst i;exact hp.2.1.mono (by omega)
  by_cases h5 : i=5
  · subst i;exact hp.2.2.mono (by omega)
  simpa only [prepared,prepareInstructions,evaluate,RationalDataflow.Instruction.update,
    Function.update_of_ne h0,Function.update_of_ne h1,Function.update_of_ne h5] using
      (hw i hi).mono (Nat.le_add_right B _)

theorem summand_bank_local (Q P W B : ℕ) (v : ℕ→Parts) (hw : WidthBank ids B v)
    (hm : ∀i,10 ≤ i → i<16 → (v i).Width W) :
    WidthBank ids (B+productWorkWidth Q P (5*(W+1))) (summand Q P v) := by
  have hp := prepared_operands_width W v hm
  have hs := product_small_width Q P (5*(W+1)) (prepared v) hp.1 hp.2.1 hp.2.2
  intro i hi
  by_cases hl : i<8
  · exact (hs i (Finset.mem_range.mpr hl)).mono (Nat.le_add_left _ _)
  · rw [summand_unchanged Q P v i (by omega)]
    exact (hw i hi).mono (Nat.le_add_right _ _)

theorem sumStep_executes (Q P W B oldQ oldN : ℕ) (v : ℕ→Parts) (hw : WidthBank ids B v)
    (hmw : ∀i,10 ≤ i → i<16 → (v i).Width W) (hg : Good ids v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : Ready ids v s)
    (hp : Phase.Runtime.Clean s.val) (hf : DyadicFloor.Clean s.val) (hm : Parameters Q P s)
    (hqo : Word s.val 652 oldQ) (hno : Word s.val 653 oldN) :
    ∃cost t,Executes input tape sumStepCode cost s t ∧ cost≤sumStepCost Q P W B oldQ oldN ∧
      Ready ids (sumStep Q P v) t ∧ Phase.Runtime.Clean t.val ∧ DyadicFloor.Clean t.val ∧
      Parameters Q P t ∧ Word t.val 652 1 ∧ Word t.val 653 P ∧
      BinaryPrecision.Frame evaluationWorkspace s.val t.val := by
  have htrace := inferred_widthTrace ids prepareInstructions prepareInstructions_valid (fun _ => B)
    v hw (64*(B+1)) (hw.mono (by omega)) (prepare_program_width B)
  obtain ⟨c0,s0,e0,hc0,b0,f0⟩ := program_executes ids prepareInstructions prepareInstructions_valid
    v (64*(B+1)) htrace input tape s hs
  change Ready ids (prepared v) s0 at b0
  have hc0' : c0≤4*operationCost (64*(B+1))+1 := by simpa only [show prepareInstructions.length=4 by rfl] using hc0
  have hp0 := hp.arithmetic_frame f0 b0
  have hf0 := hf.arithmetic_frame f0
  have hm0 := hm.arithmetic_frame f0
  have q0 := word_of_eq (f0.tapes 652 (RationalDataflow.outside_workspace ids 652 (by omega))) hqo
  have n0 := word_of_eq (f0.tapes 653 (RationalDataflow.outside_workspace ids 653 (by omega))) hno
  have hpg := evaluate_good ids prepareInstructions prepareInstructions_valid v hg (by
    simp [prepareInstructions,AdmissibleTrace,RationalDataflow.Instruction.Admissible])
  have hop := prepared_operands_width W v hmw
  obtain ⟨c1,s1,e1,hc1,b1,hp1,hf1,hm1,q1,n1,f1⟩ := product_executes Q P (5*(W+1)) (B+5*(W+1)) oldQ oldN
    (prepared v) (prepared_bank_local W B v hw hmw) hop.1 hop.2.1 hop.2.2 hpg
    input tape s0 b0 hp0 hf0 hm0 q0 n0
  change Ready ids (summand Q P v) s1 at b1
  have hsum := summand_bank_local Q P W B v hw hmw
  have hat := inferred_widthTrace ids accumulateInstructions accumulateInstructions_valid
    (fun _ => B+productWorkWidth Q P (5*(W+1))) (summand Q P v) hsum
    (64*(B+productWorkWidth Q P (5*(W+1))+1)) (hsum.mono (by omega)) (accumulate_program_width _)
  obtain ⟨c2,t,e2,hc2,b2,f2⟩ := program_executes ids accumulateInstructions accumulateInstructions_valid
    (summand Q P v) _ hat input tape s1 b1
  change Ready ids (sumStep Q P v) t at b2
  have hc2' : c2≤3*operationCost (64*(B+productWorkWidth Q P (5*(W+1))+1))+1 := by
    simpa only [show accumulateInstructions.length=3 by rfl] using hc2
  have qt := word_of_eq (f2.tapes 652 (RationalDataflow.outside_workspace ids 652 (by omega))) q1
  have nt := word_of_eq (f2.tapes 653 (RationalDataflow.outside_workspace ids 653 (by omega))) n1
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,b2,hp1.arithmetic_frame f2 b2,hf1.arithmetic_frame f2,
    hm1.arithmetic_frame f2,qt,nt,(f0.mono arithmetic_subset_evaluation).trans
      (f1.trans (f2.mono arithmetic_subset_evaluation))⟩
  unfold sumStepCost
  omega

#print axioms sumStep_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime
