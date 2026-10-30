import Maxwell.Continuum.ContinuumScalarResources
import Maxwell.Continuum.ParameterSourcePrecision

/-! The actual midpoint detuning is emitted as a dyadic Boolean word. Its
numerator and denominator have logarithmic widths, including the random index. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.RealizationParameters

attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude MasterConstants.exponent

def detuningBitCoefficient (p : Source.Parameters) : ℕ :=
  (28+204*Parameters.sourceMagnitude p+4*2^(9*Parameters.sourceMagnitude p))+
    (7+2^(12*Parameters.sourceMagnitude p))+4

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

def detuningPrecision : ℕ :=
  Parameters.tauBits (length p S hm) (spacing p S hm) (length_pos p S hm)+
    Detuning.randomBits S.nnz (count p S hm)+1

def detuningData (j : Fin (drawCount p S hm)) : Maxwell.Dyadic (detuningPrecision p S hm) :=
  ⟨2*(j.val : ℤ)+1⟩

def detuningBits (j : Fin (drawCount p S hm)) : List Bool :=
  Maxwell.Codec.nat (detuningPrecision p S hm)++Maxwell.Codec.int (detuningData p S hm j).numerator

theorem detuningData_value (j : Fin (drawCount p S hm)) :
    ((detuningData p S hm j).value : ℝ)=sample p S hm j := by
  have h := Detuning.sample_dyadic 1
    (Parameters.tauBits (length p S hm) (spacing p S hm) (length_pos p S hm))
    S.nnz (count p S hm) j.val
  have hr : (radius p S hm : ℝ)=1/(2 : ℝ)^Parameters.tauBits
      (length p S hm) (spacing p S hm) (length_pos p S hm) := by
    change ((1/(2 : ℚ)^Parameters.tauBits
      (length p S hm) (spacing p S hm) (length_pos p S hm) : ℚ) : ℝ)=_
    push_cast
    rfl
  simp only [Int.cast_one,mul_one] at h
  rw [← hr] at h
  change _=DetuningGrid.midpoint (radius p S hm) (Detuning.gridSize S.nnz (count p S hm)) j.val
  rw [h]
  simp only [detuningData,Maxwell.Dyadic.value,detuningPrecision,Rat.cast_div,Rat.cast_intCast,
    Rat.cast_pow,Rat.cast_ofNat]

theorem detuningPrecision_linear (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    detuningPrecision p S hm+2≤detuningBitCoefficient p*logSize S := by
  have ht := Parameters.source_tau_bits p S hm hm2 hu
  change Maxwell.rationalBitLength (Parameters.tau (length p S hm) (spacing p S hm)
    (length_pos p S hm))≤_ at ht
  rw [Parameters.tau_bits_exact] at ht
  have hr := Parameters.source_random_bits p S hm hm2 hu
  have hℓ := Parameters.inputLog_pos S.nnz
  change Detuning.randomBits S.nnz (count p S hm)≤_ at hr
  unfold detuningPrecision detuningBitCoefficient
  nlinarith only [ht,hr,hℓ]

theorem detuning_word_bits (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S))
    (j : Fin (drawCount p S hm)) :
    (detuningData p S hm j).numeratorBits≤detuningBitCoefficient p*logSize S ∧
    Maxwell.unsignedBitLength (2^detuningPrecision p S hm)≤detuningBitCoefficient p*logSize S := by
  have hv : |(detuningData p S hm j).value|≤(2 : ℚ)^0 := by
    apply (Rat.cast_le (K := ℝ)).mp
    rw [Rat.cast_abs,detuningData_value]
    simp only [pow_zero,Rat.cast_one]
    rw [abs_of_nonneg (sample_bounds p S hm j).1]
    exact sample_le_one p S hm j
  have hn := dyadic_numerator_bits_of_bound (detuningData p S hm j) hv
  have hp := detuningPrecision_linear p S hm hm2 hu
  rw [Maxwell.Dyadic.denominator_bitLength]
  exact ⟨(by simpa only [Nat.add_zero] using hn.trans hp),by omega⟩

theorem detuningBits_length (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S))
    (j : Fin (drawCount p S hm)) :
    (detuningBits p S hm j).length≤(4*detuningBitCoefficient p+1)*logSize S := by
  have hn := (detuning_word_bits p S hm hm2 hu j).1
  have hp := detuningPrecision_linear p S hm hm2 hu
  have hℓ := Parameters.inputLog_pos S.nnz
  have hsize : Maxwell.unsignedBitLength (detuningPrecision p S hm)≤detuningPrecision p S hm := by
    rw [Maxwell.Codec.unsignedBitLength_eq_size]
    exact Nat.size_le.mpr (Nat.lt_two_pow_self (n := detuningPrecision p S hm))
  simp only [detuningBits,List.length_append,Maxwell.Codec.nat_length,Maxwell.Codec.int_length]
  change Maxwell.signedBitLength (detuningData p S hm j).numerator≤_ at hn
  nlinarith only [hn,hp,hsize,hℓ]

#print axioms detuningData_value
#print axioms detuning_word_bits
#print axioms detuningBits_length

end Maxwell.Continuum.RealizationParameters
