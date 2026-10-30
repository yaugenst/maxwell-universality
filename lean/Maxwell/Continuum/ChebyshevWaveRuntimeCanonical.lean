import Maxwell.Continuum.ChebyshevWaveRuntimeRounding
import Maxwell.Continuum.RationalDataflowIntegerCanonical
import Maxwell.Continuum.ChebyshevWaveBits

/-! Canonical cache words for the rounded Fourier coefficients. The actual
machine removes cancellation in the two raw numerator channels before storage. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator RationalDataflow RationalTaylor
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def canonicalPairCode : Code := .seq (IntegerCanonical.code 8 8) (IntegerCanonical.code 9 9)
def canonicalPairValues (v : ℕ→Parts) : ℕ→Parts :=
  Function.update (Function.update v 8 (IntegerCanonical.result (v 8))) 9 (IntegerCanonical.result (v 9))
def canonicalPairCost (B : ℕ) : ℕ := operationCost B+operationCost (B+1)

theorem canonicalPair_width (B : ℕ) (v : ℕ→Parts) (hw : WidthBank ids B v) :
    WidthBank ids (B+1) (canonicalPairValues v) :=
  ((hw.mono (by omega)).update 8 (IntegerCanonical.result_width B _ (hw 8 (by decide)))).update
    9 (IntegerCanonical.result_width B _ (hw 9 (by decide)))

theorem canonicalPair_good (v : ℕ→Parts) (hg : Good ids v) : Good ids (canonicalPairValues v) :=
  (hg.update 8 (IntegerCanonical.result_valid _)).update 9 (IntegerCanonical.result_valid _)

theorem canonical_pair_executes (Q P B : ℕ) (v : ℕ→Parts) (hw : WidthBank ids B v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (hs : LoopReady Q P v s) :
    ∃cost t,Executes input tape canonicalPairCode cost s t ∧ cost ≤ canonicalPairCost B ∧
      LoopReady Q P (canonicalPairValues v) t ∧
      BinaryPrecision.Frame (RationalDataflow.workspace ids) s.val t.val := by
  obtain ⟨c0,s0,e0,hc0,r0,f0⟩ := IntegerCanonical.executes ids 8 8 (by decide) (by decide) v B hw input tape s hs.ready
  have lr0 := hs.arithmetic_frame f0 r0
  have hw0 : WidthBank ids (B+1) (Function.update v 8 (IntegerCanonical.result (v 8))) :=
    (hw.mono (by omega)).update 8 (IntegerCanonical.result_width B _ (hw 8 (by decide)))
  obtain ⟨c1,t,e1,hc1,r1,f1⟩ := IntegerCanonical.executes ids 9 9 (by decide) (by decide) _ (B+1) hw0
    input tape s0 lr0.ready
  have rt : LoopReady Q P (canonicalPairValues v) t := by
    simpa only [canonicalPairValues,Function.update_of_ne (by decide : (9:ℕ)≠8)] using lr0.arithmetic_frame f1 r1
  exact ⟨c0+c1,t,e0.seq e1,by unfold canonicalPairCost;omega,rt,f0.trans f1⟩

def encodedValues (Q P grid : ℕ) (v : ℕ→Parts) : ℕ→Parts :=
  canonicalPairValues (roundPairValues P (cosineValues Q P grid v))

theorem encodedValues_correct (grid : ℕ) [NeZero grid] (q : ℚ) (j Q P : ℕ) (v : ℕ→Parts)
    (hv : Good ids v) (hi : SumInput grid q (j:ℤ) 0 v) (hz0 : (v 8).value=0) (hz1 : (v 9).value=0) :
    encodedValues Q P grid v 8=Parts.literal (((roundComplex P (rationalWaveCosineCoefficient grid q Q P j)).1.numerator):ℚ) ∧
    encodedValues Q P grid v 9=Parts.literal (((roundComplex P (rationalWaveCosineCoefficient grid q Q P j)).2.numerator):ℚ) := by
  have hc := roundedCosine_correct grid q j Q P v hv hi hz0 hz1
  have hd := roundPairValues_denominator P (cosineValues Q P grid v)
  simp only [encodedValues,canonicalPairValues,Function.update_self,
    Function.update_of_ne (by decide : (8:ℕ)≠9)]
  rw [IntegerCanonical.result_eq_literal_value _ hd.1,IntegerCanonical.result_eq_literal_value _ hd.2,hc.1,hc.2]
  exact ⟨rfl,rfl⟩

theorem encodedValues_wave (q : ℚ) (Q N j : ℕ) (v : ℕ→Parts) (hv : Good ids v)
    (hi : SumInput (waveGrid (8*Q) N) q (j:ℤ) 0 v) (hz0 : (v 8).value=0) (hz1 : (v 9).value=0) :
    encodedValues Q (waveWorkBits (8*Q) N) (waveGrid (8*Q) N) v 8=
      Parts.literal ((waveRoundedCoefficient q Q N j).1.numerator:ℚ) ∧
    encodedValues Q (waveWorkBits (8*Q) N) (waveGrid (8*Q) N) v 9=
      Parts.literal ((waveRoundedCoefficient q Q N j).2.numerator:ℚ) :=
  encodedValues_correct _ q j Q _ v hv hi hz0 hz1

theorem integer_literal_width (k : ℤ) (B : ℕ) (h : signedBitLength k ≤ B) (hB : 1 ≤ B) :
    (Parts.literal (k:ℚ)).Width B := by
  apply Parts.literal_width
  constructor
  · simp only [Rat.num_intCast]
    unfold signedBitLength at h
    rw [Codec.unsignedBitLength_eq_size,←Nat.size_eq_bits_len] at h
    omega
  · simpa only [Rat.den_intCast,show (1:ℕ).bits.length=1 by decide] using hB

theorem encodedValues_wave_width (q : ℚ) (Q N j : ℕ) (hq : |q| ≤ Q) (hj : j ≤ waveDegree (8*Q) N)
    (v : ℕ→Parts) (hv : Good ids v) (hi : SumInput (waveGrid (8*Q) N) q (j:ℤ) 0 v)
    (hz0 : (v 8).value=0) (hz1 : (v 9).value=0) :
    (encodedValues Q (waveWorkBits (8*Q) N) (waveGrid (8*Q) N) v 8).Width (waveWorkBits (8*Q) N+7) ∧
    (encodedValues Q (waveWorkBits (8*Q) N) (waveGrid (8*Q) N) v 9).Width (waveWorkBits (8*Q) N+7) := by
  have he := encodedValues_wave q Q N j v hv hi hz0 hz1
  rw [he.1,he.2]
  have hb := waveRoundedCoefficient_bits q Q N j hq hj
  exact ⟨integer_literal_width _ _ hb.1 (by omega),integer_literal_width _ _ hb.2 (by omega)⟩

#print axioms canonical_pair_executes
#print axioms encodedValues_wave
#print axioms encodedValues_wave_width
end Maxwell.Continuum.Profile.WaveMachine.Runtime
