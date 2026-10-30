import Maxwell.Continuum.ContinuumCalibrationResources
import Maxwell.Continuum.ParameterSourceWords
import Maxwell.Continuum.RationalArithmeticWidths

/-! Literal rational output widths for the selected energy and field
residual tolerance. Magnitude estimates alone are not used as width bounds. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.RealizationParameters

attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude MasterConstants.exponent

private theorem width_nat (n : ℕ) : RationalWords.Width (n : ℚ) (n.bits.length+1) := by
  constructor
  · simp only [Rat.num_natCast,Int.natAbs_natCast]
    omega
  · simp only [Rat.den_natCast]
    change 1≤n.bits.length+1
    omega

private theorem width_bits {q : ℚ} {B : ℕ} (h : RationalWords.Width q B) :
    Maxwell.rationalBitLength q≤2*B+1 := by
  simp only [Maxwell.rationalBitLength,Maxwell.signedBitLength,
    Maxwell.Codec.unsignedBitLength_eq_size,← Nat.size_eq_bits_len]
  have hn := h.num
  have hd := h.den
  omega

def energyWordCoefficient (p : Source.Parameters) : ℕ :=
  2*(2^66+24*outputBitCoefficient p+5+2*(45*Parameters.sourceMagnitude p+14)+1)+1

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

theorem energy_word_bits (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    Maxwell.rationalBitLength (energy p S hm)≤energyWordCoefficient p*logSize S := by
  have hLQ : (length p S hm : ℚ)≠0 := by exact_mod_cast (length_pos p S hm).ne'
  have hi := (width_nat (length p S hm)).inv hLQ
  have he : RationalWords.Width (energy p S hm)
    (2^66+24*energyPrecision p S hm+5+
      ((length p S hm).bits.length+1+((length p S hm).bits.length+1))+1) := by
    simpa only [energy,pow_two] using
      (Calibration.calibratedEdge_center_width (energyPrecision p S hm)).sub (hi.mul hi)
  have hb := width_bits he
  have hn := (Parameters.source_bits p S hm hm2 hu).1
  change (length p S hm).bits.length≤45*Parameters.sourceMagnitude p+6*logSize S+7 at hn
  have hp := (selected_precisions_linear p S hm hm2 hu).1
  have hℓ := Parameters.inputLog_pos S.nnz
  have hl : (length p S hm).bits.length+1≤(45*Parameters.sourceMagnitude p+14)*logSize S := by
    nlinarith only [hn,hℓ]
  unfold energyWordCoefficient
  nlinarith only [hb,hp,hl,hℓ]

def residualDenominator : ℕ :=
  2^27*64*S.nnz*count p S hm*Parameters.sourceErrorDen p S hm*
    2^Parameters.tauBits (length p S hm) (spacing p S hm) (length_pos p S hm)

private theorem errorBudget_reciprocal (m N E t : ℕ) :
    Parameters.errorBudget m N (1/(E : ℚ)) (1/(2 : ℚ)^t) =
      ((2^27*64*m*N*E*2^t : ℕ) : ℚ)⁻¹ := by
  simp only [Parameters.errorBudget,Parameters.inverseBudget,div_eq_mul_inv,
    Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,mul_inv_rev,inv_inv,one_mul]
  ring

theorem residual_reciprocal : residual p S hm=(residualDenominator p S hm : ℚ)⁻¹ := by
  change Parameters.errorBudget S.nnz (count p S hm) (Parameters.sourceInput p S hm).epsilon
    (radius p S hm)=_
  rw [Parameters.source_epsilon_eq]
  have hτ : radius p S hm=1/(2 : ℚ)^Parameters.tauBits
      (length p S hm) (spacing p S hm) (length_pos p S hm) := rfl
  rw [hτ]
  exact errorBudget_reciprocal _ _ _ _

theorem residualDenominator_pos : 0<residualDenominator p S hm := by
  have hN := Parameters.sourceSpectralBudget_pos p S hm
  have hE := Parameters.sourceErrorDen_pos p S hm
  unfold residualDenominator
  change 0<2^27*64*S.nnz*Parameters.sourceSpectralBudget p S hm*Parameters.sourceErrorDen p S hm*_
  positivity

theorem residualDenominator_binary (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    residualDenominator p S hm≤2^scaleBits p S := by
  have hres : (0 : ℚ)<residual p S hm := by exact_mod_cast residual_pos p S hm
  have hh := (inv_le_inv₀ hres (by positivity : (0 : ℚ)<(1/2)^scaleBits p S)).mpr
    (residual_binary p S hm hm2 hu)
  rw [residual_reciprocal,inv_inv] at hh
  have he : ((1/2 : ℚ)^scaleBits p S)⁻¹=(2 : ℚ)^scaleBits p S := by
    rw [← inv_pow]
    norm_num
  rw [he] at hh
  exact_mod_cast hh

theorem residual_word_bits (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    Maxwell.rationalBitLength (residual p S hm)≤(analysisBits p+4)*logSize S := by
  rw [residual_reciprocal,Parameters.inverse_nat_rational_bits (residualDenominator_pos p S hm)]
  have hb := Nat.size_le_size (residualDenominator_binary p S hm hm2 hu)
  rw [Nat.size_pow,← Nat.size_eq_bits_len] at hb
  have hℓ := Parameters.inputLog_pos S.nnz
  unfold scaleBits at hb
  nlinarith only [hb,hℓ]

#print axioms energy_word_bits
#print axioms residual_reciprocal
#print axioms residual_word_bits

end Maxwell.Continuum.RealizationParameters
