import Maxwell.Continuum.CalibrationNormRootValues

/-! Executed normalization scalar from the actual signed norm accumulator
and the actual common denominator of the finite power output. -/

namespace Maxwell.Continuum.Calibration.PowerMachine.BufferNorm.Root

open Maxwell.Cost Maxwell.Cost.Structured
open RationalAccumulator (Word)
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def code : Code := .seq RationalMagnitude.program
  (.seq (NatAssign.code preparePlan) RationalRoot.Raw.code)
def costBound (N W : ℕ) : ℕ := 2^150*(N+W+10)^7

theorem executes (p m D base N W : ℕ) (hDpos : 0<D)
    (hp : p.bits.length≤W) (hm : m.bits.length≤W) (hD : D.bits.length≤W)
    (hbase : base.bits.length≤W) (hN : N.bits.length≤W)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : NatAssign.Bank ids (inputValues p m D base N) s.val) (hz : NatAssign.Scratch s.val) :
    ∃ cost t, ∃ numerator denominator : ℕ,
      Executes input tape code cost s t ∧ cost≤costBound N W ∧
      Word t.val 32 numerator ∧ Word t.val 548 denominator ∧ 0<denominator ∧
      (numerator:ℚ)/denominator=
        sqrtRationalCenter ((IntegerNormSquare.magnitude p m:ℚ)/(D^2:ℕ)) N ∧
      denominator.bits.length≤2*W+2*N+3 ∧
      Word t.val 549 D ∧
      NatAssign.Bank NaturalRoot.fullIds (NaturalRoot.doneValues (normRadicand p m D N)) t.val ∧
      NatAssign.Scratch t.val ∧ BinaryPrecision.Frame changed s.val t.val := by
  obtain ⟨c0,u,e0,hc0,b0,z0,f0,_⟩ := RationalMagnitude.executes ids (by decide) ids_ge
    (inputValues p m D base N) (by simp [inputValues]) input tape s hs hz
  have mag30 : inputValues p m D base N 30=p := by simp [inputValues]
  have mag31 : inputValues p m D base N 31=m := by simp [inputValues]
  rw [mag30,mag31] at hc0 b0
  change NatAssign.Bank ids (magnitudeValues p m D base N) u.val at b0
  obtain ⟨c1,v,e1,hc1,b1,z1,f1⟩ := NatAssign.executes ids ids_ge preparePlan preparePlan_valid
    (magnitudeValues p m D base N) input tape u b0 z0
  have price := NatAssign.price_bound ids preparePlan preparePlan_valid
    (magnitudeValues p m D base N) (W+1)
      (fun i _ => magnitude_width p m D base N W hp hm hD hbase hN i)
      (by simp [preparePlan,NatAssign.Instruction.literalWidth])
  have cost1 : c1≤3000*8^15*(W+3)^2 := by
    simpa only [preparePlan,List.length_cons,List.length_nil,Nat.add_assoc] using hc1.trans price
  rw [preparePlan_values] at b1
  have rootBank : NatAssign.Bank RationalRoot.Raw.ids
      (RationalRoot.Raw.inputValues (IntegerNormSquare.magnitude p m) (D^2) N) v.val := by
    intro i hi
    have h549 : i≠549 := by
      simp only [RationalRoot.Raw.ids,RationalRoot.ids,NaturalRoot.fullIds,NaturalRoot.ids,
        RationalCanonicalBank.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
        Finset.mem_Icc] at hi
      omega
    simpa only [preparedValues,ite_eq_right h549] using b1 i (Finset.mem_union_left _ hi)
  have hmag : (IntegerNormSquare.magnitude p m).bits.length≤2*W+2 := by
    have h := (IntegerNormSquare.magnitude_bits_length_le p m).trans
      (Nat.add_le_add_right (max_le hp hm) 1)
    omega
  have hden : (D^2).bits.length≤2*W+2 := by
    have h := RationalAccumulator.bits_mul_le D D
    rw [pow_two]
    omega
  obtain ⟨c2,t,num,den,e2,hc2,wn,wd,hd,value,denWidth,rootBankOut,z2,f2⟩ := RationalRoot.Raw.executes
    (IntegerNormSquare.magnitude p m) (D^2) N (2*W+2) (by positivity)
      hmag hden (hN.trans (by omega)) input tape v rootBank z1
  have saved : Word t.val 549 D := by
    simpa [preparedValues] using RationalAccumulator.word_of_eq (f2.tapes 549 (by decide))
      (b1 549 (by decide))
  refine ⟨c0+(c1+c2),t,num,den,e0.seq (e1.seq e2),?_,wn,wd,hd,value,by omega,saved,rootBankOut,z2,
    (f0.mono (by decide)).trans ((f1.mono (by decide)).trans (f2.mono (by decide)))⟩
  have cost0 : c0≤300*(2*W+4) := hc0.trans (Nat.mul_le_mul_left _ (by omega))
  apply (Nat.add_le_add cost0 (Nat.add_le_add cost1 hc2)).trans
  unfold RationalRoot.Raw.costBound costBound
  ring_nf
  omega

theorem buffer_value {n : ℕ} (b : Maxwell.Cost.CalibrationMatrix.Buffers n) (D N : ℕ) :
    sqrtRationalCenter ((IntegerNormSquare.magnitude
      (Maxwell.Cost.CalibrationMatrix.Pairing.positive (bufferChannels b) (bufferChannels b))
      (Maxwell.Cost.CalibrationMatrix.Pairing.negative (bufferChannels b) (bufferChannels b)):ℚ)/(D^2:ℕ)) N=
        sqrtRationalCenter (∑ i, (((bufferChannels b).value i:ℚ)/D)^2) N := by
  rw [rational_magnitude_norm]

#print axioms executes
#print axioms buffer_value

end Maxwell.Continuum.Calibration.PowerMachine.BufferNorm.Root
