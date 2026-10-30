import Maxwell.Continuum.CalibrationRootGridPrepared

/-! One fixed program computes a literal rational root Fourier coefficient.
It creates its own countdown, evaluates every grid sample, and divides by the
computed grid cube. No sampled-value array or execution oracle is supplied. -/
namespace Maxwell.Continuum.RationalDataflow.RootGrid
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

def coefficientCode : Code := .seq startCode (.seq sumCode finishCode)
def coefficientWorkspace (S : Finset ℕ) : Finset ℕ := startWorkspace S∪sumWorkspace S
def coefficientRawWidth (grid N B I : ℕ) : ℕ := 4*(loopWidth grid N (runtimeWidth B) I 0+1)
def coefficientCost (grid N B I : ℕ) : ℕ :=
  stageCost B+2*operationCost I+1+
    (sumCost grid N (runtimeWidth B) I (grid^3).bits.length+
      2^108*(loopWidth grid N (runtimeWidth B) I 0+3)^2)

structure CoefficientState (S : Finset ℕ) (grid N : ℕ) [NeZero grid] (frequency : Fin 3→ℤ) (B I : ℕ)
    (initial : ℕ→Parts) (s : Store) where
  parts : ℕ→Parts
  naturals : ℕ→ℕ
  rational_bank : Ready S parts s
  good : Good S parts
  width : WidthBank S (coefficientRawWidth grid N B I) parts
  facts : InputFacts grid frequency (runtimeWidth B) naturals
  natural_bank : NatAssign.Bank ids naturals s.val
  external : ∀i,8 ≤ i → i≠10 → i≠11 → i≠12 → parts i=initial i
  real_value : (parts 10).value=(Calibration.rationalRootCoefficient grid (initial 9).value N frequency).re.center
  imag_value : (parts 11).value=(Calibration.rationalRootCoefficient grid (initial 9).value N frequency).im.center
  scratch : ∀i,i<5 → Blank s.val i
  glue : Glue.Clean s.val
  phase : Phase.Runtime.Clean s.val
  precision_glue : Word s.val 640 N
  phase_range : Word s.val 652 1
  precision_phase : Word s.val 653 N
  cube : Word s.val 343 (grid^3)
  one : Word s.val 344 1
  counterWord : List Bool
  counter : BankArray.Word s.val 342 counterWord
  counter_length : counterWord.length≤(grid^3).bits.length

theorem coefficient_executes (S : Finset ℕ) (hS : coefficientInputs⊆S)
    (grid N : ℕ) [NeZero grid] (frequency : Fin 3→ℤ) (B I : ℕ) (hB : 1≤B) (hI : 1≤I)
    (n : ℕ→ℕ) (initial : ℕ→Parts)
    (hgrid : n 331=grid)
    (hfrequency : ∀i,![n 336,n 337,n 338] i=
      ((-(PeriodicSampling.Product.frequency grid frequency)) i).val)
    (hzero : ∀i∈NaturalQuotient.workPorts,n i=0)
    (hn : ∀i∈ids,(n i).bits.length≤B) (hcw : ∀i∈clockIds,(n i).bits.length≤B)
    (hw : WidthBank S I initial) (hg : Good S initial)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : Ready S initial s) (hb : NatAssign.Bank ids n s.val) (hc : NatAssign.Bank clockIds n s.val)
    (hz : ∀i,i<5 → Blank s.val i) (hglue : Glue.Clean s.val) (hphase : Phase.Runtime.Clean s.val)
    (hp : Word s.val 640 N) (hq : Word s.val 652 1) (hprec : Word s.val 653 N) :
    ∃cost t,Executes input tape coefficientCode cost s t ∧ cost≤coefficientCost grid N B I ∧
      Nonempty (CoefficientState S grid N frequency B I initial t) ∧
      BinaryPrecision.Frame (coefficientWorkspace S) s.val t.val := by
  have hsums : sumInputs⊆S := Finset.subset_union_left.trans hS
  have hsize := cube_width n grid B hB hcw hgrid
  have hfacts := inputFacts grid B frequency n hgrid hfrequency hzero hn
  obtain ⟨c0,s0,e0,h0,r0,g0,w0,b0,k0,z0,gl0,ph0,p0,q0,n0,f0⟩ :=
    start_executes S hsums N B I n initial hB hI hcw hw hg input tape s hs hb hc hz hglue hphase hp hq hprec
  have word342 : Word s0.val 342 (grid^3) := by
    simpa only [(clockValues_result n).2.1,hgrid] using k0 342 (by decide)
  have word343 : Word s0.val 343 (grid^3) := by
    simpa only [(clockValues_result n).2.2.1,hgrid] using k0 343 (by decide)
  have word344 : Word s0.val 344 1 := by
    simpa only [(clockValues_result n).2.2.2] using k0 344 (by decide)
  rcases word342 with ⟨origin,h342⟩
  obtain ⟨c1,s1,lastWord,e1,hstate,lastEq,lastLength,h1,f1⟩ := sum_executes S hsums grid N frequency
    (runtimeWidth B) I n (zeroValues initial) hfacts w0 g0 hsize (grid^3).bits origin
    (addressValue_bits _) input tape s0 r0 b0 z0 gl0 ph0 p0 q0 n0 h342
  rcases hstate with ⟨state⟩
  have word343' := word_of_eq (f1.tapes 343 (normalization_outside_sum S 343 (Or.inl rfl))) word343
  have word344' := word_of_eq (f1.tapes 344 (normalization_outside_sum S 344 (Or.inr rfl))) word344
  have hW := loopWidth_ge grid N (runtimeWidth B) I 0
  have hcub : (grid^3).bits.length≤loopWidth grid N (runtimeWidth B) I 0 :=
    hsize.trans ((by unfold dataWidth naturalWidth;omega : runtimeWidth B≤dataWidth (runtimeWidth B) I).trans hW.2.2.1)
  obtain ⟨c2,t,e2,h2,r2,g2,w2,f2⟩ := finish_executes S hS grid _
    (Nat.pos_of_ne_zero (NeZero.ne grid)) state.parts state.width state.good (by omega)
    hcub input tape s1 state.rational_bank word344' word343'
  have exactValues := finishValues_exact state (zeroValues_zero initial)
  have scaleEq : (zeroValues initial 9).value=(initial 9).value :=
    congrArg Parts.value (zeroValues_other initial 9 ⟨by decide,by decide⟩)
  rw [scaleEq] at exactValues
  have z2 (i : ℕ) (hi : i<5) : Blank t.val i := by
    by_cases h4 : i<4
    · exact r2.2 i h4
    have he : i=4 := by omega
    subst i
    exact blank_of_eq ((f2.mono (rational_subset_product S)).tapes 4 (four_outside_product S)) (state.scratch 4 (by decide))
  let result : CoefficientState S grid N frequency B I initial t := {
    parts := finishValues grid state.parts
    naturals := state.naturals
    rational_bank := r2
    good := g2
    width := w2
    facts := state.facts
    natural_bank := fun i hi => word_of_eq (f2.tapes i (ids_outside_rational S i hi)) (state.natural_bank i hi)
    external := by
      intro i hi h10 h11 h12
      rw [finishValues_other _ _ _ ⟨h10,h11,h12⟩,state.external i hi h10 h11,
        zeroValues_other initial i ⟨h10,h11⟩]
    real_value := exactValues.1
    imag_value := exactValues.2
    scratch := z2
    glue := RootSample.glue_clean_arithmetic state.glue f2 r2
    phase := Phase.Runtime.Clean.arithmetic_frame state.phase f2 r2
    precision_glue := word_of_eq (f2.tapes 640 (FractionWord.outside S 640 (by decide))) state.precision_glue
    phase_range := word_of_eq (f2.tapes 652 (FractionWord.outside S 652 (by decide))) state.phase_range
    precision_phase := word_of_eq (f2.tapes 653 (FractionWord.outside S 653 (by decide))) state.precision_phase
    cube := word_of_eq (f2.tapes 343 (FractionWord.outside S 343 (by decide))) word343'
    one := word_of_eq (f2.tapes 344 (FractionWord.outside S 344 (by decide))) word344'
    counterWord := lastWord
    counter := ⟨origin,(f2.tapes 342 (FractionWord.outside S 342 (by decide))).trans lastEq⟩
    counter_length := le_of_eq lastLength }
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,⟨result⟩,?_⟩
  · unfold coefficientCost
    omega
  · exact (f0.mono Finset.subset_union_left).trans
      ((f1.mono Finset.subset_union_right).trans
        (f2.mono ((rational_subset_sum S).trans Finset.subset_union_right)))

#print axioms coefficient_executes
end Maxwell.Continuum.RationalDataflow.RootGrid
