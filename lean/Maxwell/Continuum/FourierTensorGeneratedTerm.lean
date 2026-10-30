import Maxwell.Continuum.FourierTensorDirectReturn

/-! A literal tensor summand, including all three wave computations,
is executed from its stored Fourier frequency and amplitude. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow
open RationalDataflow.PartArray
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

theorem FactorReady.congr {n D Q N : ℕ} {a : Table n} {b : Table (2*D)}
    {v w : ℕ→Parts} {s : Store} (h : FactorReady a Q N b v s)
    (he : ∀i∈tensorBank,v i=w i) : FactorReady a Q N b w s :=
  { h with ready := h.ready.congr he }

def FactoredInputs {B : ℕ} (v : ℕ→Parts) (q : Fin 3→ℚ) (amp : ComplexDyadic B)
    (Q N : ℕ) (j : Fin 3→ℕ) : Prop :=
  v 23=Parts.literal (amp.1.numerator:ℚ) ∧ v 24=Parts.literal (amp.2.numerator:ℚ) ∧
  ∀i : Fin 3,v (25+2*i.val)=waveCacheReal (q i) Q N (j i) ∧
    v (26+2*i.val)=waveCacheImag (q i) Q N (j i)

theorem FactoredInputs.valid {B : ℕ} {v : ℕ→Parts} {q : Fin 3→ℚ} {amp : ComplexDyadic B}
    {Q N : ℕ} {j : Fin 3→ℕ} (h : FactoredInputs v q amp Q N j) :
    ∀i,23 ≤ i → i ≤ 30 → (v i).Valid := by
  have h0 := h.2.2 0
  have h1 := h.2.2 1
  have h2 := h.2.2 2
  change v 25=_ ∧ v 26=_ at h0
  change v 27=_ ∧ v 28=_ at h1
  change v 29=_ ∧ v 30=_ at h2
  intro i hi hi'
  interval_cases i <;>
    simp only [h.1,h.2.1,h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,waveCacheReal,waveCacheImag,
      Parts.literal_valid]

theorem FactoredInputs.term {B : ℕ} {v : ℕ→Parts} {q : Fin 3→ℚ} {amp : ComplexDyadic B}
    {Q N : ℕ} {j : Fin 3→ℕ} (h : FactoredInputs v q amp Q N j) :
    tensorTerm (valueBank v)=
      ((complexDyadicMul amp (complexDyadicTriple (fun i => waveRoundedCoefficient (q i) Q N (j i)))).1.numerator:ℚ) := by
  have h0 := h.2.2 0
  have h1 := h.2.2 1
  have h2 := h.2.2 2
  change v 25=_ ∧ v 26=_ at h0
  change v 27=_ ∧ v 28=_ at h1
  change v 29=_ ∧ v 30=_ at h2
  simp only [tensorTerm,valueBank,h.1,h.2.1,h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,
    waveCacheReal,waveCacheImag,Parts.literal_value]
  exact TensorMachine.realProduct_numerators amp _ _ _

theorem FactoredInputs.denominator {B : ℕ} {v : ℕ→Parts} {q : Fin 3→ℚ} {amp : ComplexDyadic B}
    {Q N : ℕ} {j : Fin 3→ℕ} (h : FactoredInputs v q amp Q N j) :
    (termReturned v 32).denominator=(v 32).denominator := by
  have h0 := h.2.2 0
  have h1 := h.2.2 1
  have h2 := h.2.2 2
  change v 25=_ ∧ v 26=_ at h0
  change v 27=_ ∧ v 28=_ at h1
  change v 29=_ ∧ v 30=_ at h2
  rw [termReturned_eq,ite_eq_right (by decide : ¬32<7)]
  simp [termBody,termInstructions,Control.prepend,Control.evaluate,Instruction.update,
    BinaryOp.eval,Parts.add,Parts.sub,Parts.mul,h.1,h.2.1,h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,
    waveCacheReal,waveCacheImag,Parts.literal]

def generatedTermCode : Code := .seq axesCode termReturnCode
def generatedTermCost (Q N A W : ℕ) (j : Fin 3→ℕ) : ℕ :=
  axesCost Q N W j+termReturnCost A W

theorem generatedTerm_executes {n B : ℕ} (a : Table n) (Q N A W : ℕ)
    (b : Table (2*(waveDegree (8*Q) N+1)))
    (hm : b.MetadataWidth (producerWidth Q N W)) (hsep : b.Separated) (hdisjoint : a.SeparatedFrom b)
    (hfit : waveWorkBits (8*Q) N+7 ≤ addressValue b.width)
    (v : ℕ→Parts) (hw : WidthBank tensorBank W v) (hWA : W ≤ A) (ha : (v 32).Width A)
    (q : Fin 3→ℚ) (j : Fin 3→ℕ) (amp : ComplexDyadic B)
    (hinputs : AxisInputs v q j)
    (ha0 : v 23=Parts.literal (amp.1.numerator:ℚ)) (ha1 : v 24=Parts.literal (amp.2.numerator:ℚ))
    (hvalid : (v 32).Valid) (hq : ∀i,|q i| ≤ Q) (hj : ∀i,j i<waveDegree (8*Q) N+1)
    (hQ : Q.bits.length ≤ W) (hN : N.bits.length ≤ W) (hW : 6 ≤ W)
    (hprecision : waveWorkBits (8*Q) N+7 ≤ W) (hgrid : (waveGrid (8*Q) N).bits.length ≤ W)
    (oldIndex : ℕ) (hold : oldIndex.bits.length ≤ W)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hs : FactorReady a Q N b v s) (hr : Ready termBank v s) (hindex : Word s.val 1048 oldIndex) :
    ∃cost t w output,Executes input tape generatedTermCode cost s t ∧
      cost ≤ generatedTermCost Q N A W j ∧ FactorReady a Q N output w t ∧
      Ready termBank w t ∧ WidthBank tensorBank W w ∧ (w 32).Width (A+22*W+23) ∧
      CacheTableMetadata output b ∧ AxisInputs w q j ∧ (w 32).Valid ∧
      (w 32).denominator=(v 32).denominator ∧
      (w 32).value=(v 32).value+
        ((complexDyadicMul amp (complexDyadicTriple (fun i => waveRoundedCoefficient (q i) Q N (j i)))).1.numerator:ℚ) ∧
      Word t.val 1048 (j 2) := by
  obtain ⟨c0,s0,v0,b0,e0,h0,r0,w0,m0,in0,factors,a0,a1,_,index0⟩ := axes_executes a Q N W b hm hsep
    hdisjoint hfit v hw q j hinputs hq hj hQ hN hW hprecision hgrid oldIndex hold input tape s hs hindex
  let u := accumulatorValues v0 v
  have hu (i : ℕ) (hi : i∈tensorBank) : u i=v0 i := by simp only [u,accumulatorValues,ite_eq_left hi]
  have hu32 : u 32=v 32 := by simp only [u,accumulatorValues,ite_eq_right (by decide : 32∉tensorBank)]
  have ur : Ready termBank u s0 := axes_accumulator_ready e0 hr r0.ready
  have uf : FactorReady a Q N b0 u s0 := r0.congr (fun i hi => (hu i hi).symm)
  have uw : WidthBank tensorBank W u := fun i hi => by rw [hu i hi];exact w0 i hi
  have uwA : WidthBank termBank A u := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl|hi
    · simpa only [hu32] using ha
    · exact (uw i hi).mono hWA
  have uinputs : AxisInputs u q j := by
    intro i
    have ilt := i.isLt
    rw [hu (20+i.val) (by simp [tensorBank,Finset.mem_Ico];omega),
      hu (17+i.val) (by simp [tensorBank,Finset.mem_Ico];omega)]
    exact in0 i
  have ufactors : FactoredInputs u q amp Q N j := by
    refine ⟨(hu 23 (by decide)).trans (a0.trans ha0),
      (hu 24 (by decide)).trans (a1.trans ha1),?_⟩
    intro i
    have ilt := i.isLt
    rw [hu (25+2*i.val) (by simp [tensorBank,Finset.mem_Ico];omega),
      hu (26+2*i.val) (by simp [tensorBank,Finset.mem_Ico];omega)]
    exact factors i
  obtain ⟨c1,t,e1,h1,r1,ur1,w1,acc1,frame1⟩ := termReturn_executes a b0 u A W (by omega) uw uwA input tape s0 uf ur
  have val := termReturned_value u ufactors.valid (by simpa only [hu32] using hvalid)
  refine ⟨c0+c1,t,termReturned u,b0,e0.seq e1,Nat.add_le_add h0 h1,r1,ur1,w1,acc1,m0,?_,val.1,?_,
    ?_,word_of_eq (frame1.tapes 1048 (by decide)) index0⟩
  · intro i
    have ilt := i.isLt
    rw [termReturned_high u (20+i.val) (by omega) (by omega),
    termReturned_high u (17+i.val) (by omega) (by omega)]
    exact uinputs i
  · exact ufactors.denominator.trans (congrArg Parts.denominator hu32)
  · rw [val.2,hu32,ufactors.term]

#print axioms generatedTerm_executes
end Maxwell.Continuum.Profile.WaveMachine.Runtime
