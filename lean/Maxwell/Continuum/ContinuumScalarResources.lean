import Maxwell.Continuum.FiniteAuxiliaryDyadicBits
import Maxwell.Continuum.ContinuumCalibrationResources
import Maxwell.Continuum.ContinuumRealizationConcreteMessages

/-! Literal dyadic numerator and denominator widths of all selected well
strengths and nonzero source amplitudes. Intermediate rational calibration
channels are rounded before they are emitted as physical coefficients. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.RealizationParameters

open FiniteAuxiliary Calibration Maxwell.Composition
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude MasterConstants.exponent

def onsitePrecisionCoefficient (p : Source.Parameters) : ℕ :=
  4*(Nat.clog 2 (calibrationBaseCoefficient p+1)+6)+4*calibrationBaseCoefficient p+1

def scalarWordCoefficient (p : Source.Parameters) : ℕ :=
  onsitePrecisionCoefficient p+outputBitCoefficient p+4

private theorem word_linear {n P A B ℓ : ℕ} (hn : n≤P+3) (hP : P≤A*ℓ) (hℓ : 0<ℓ) :
    n≤(A+B+4)*ℓ := by nlinarith only [hn,hP,hℓ,Nat.zero_le B]

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

theorem onsitePrecision_linear (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    onsitePrecision (length p S hm) (spacing p S hm) (length_pos p S hm) ≤
      onsitePrecisionCoefficient p*logSize S := by
  have hs := calibration_base_scales p S hm hm2 hu
  have hℓ := Parameters.inputLog_pos S.nnz
  have hl := FiniteAlgorithm.lengthBits_polynomial hℓ 6 hs.1
  have hLnat : length p S hm≤2^lengthBits (length p S hm) := by
    exact_mod_cast lengthBits_bound (length p S hm)
  have hp := onsite_precision_binary (length_pos p S hm) hLnat (spacing p S hm)
  unfold onsitePrecisionCoefficient
  nlinarith only [hp,hl,hs.2.1,hℓ]

theorem wellStrength_word_bits (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S))
    (C : Enclosures p S hm) (hb : S.source≠0)
    (i : SourceDecoration.Vertex S (precision p S hm)) :
    (strengthData p S hm C.mode C.coupling i).numeratorBits≤scalarWordCoefficient p*logSize S ∧
    Maxwell.unsignedBitLength
      (2^onsitePrecision (length p S hm) (spacing p S hm) (length_pos p S hm))≤
        scalarWordCoefficient p*logSize S := by
  have hvalue : |(strengthData p S hm C.mode C.coupling i).value|≤(2 : ℚ)^0 := by
    simpa only [pow_zero,Enclosures.wellStrength,strength] using wellStrength_abs p S hm C hb i
  have hbnum := dyadic_numerator_bits_of_bound (strengthData p S hm C.mode C.coupling i) hvalue
  change (strengthData p S hm C.mode C.coupling i).numeratorBits≤
    onsitePrecision (length p S hm) (spacing p S hm) (length_pos p S hm)+0+2 at hbnum
  have hp := onsitePrecision_linear p S hm hm2 hu
  have hℓ := Parameters.inputLog_pos S.nnz
  rw [Maxwell.Dyadic.denominator_bitLength]
  refine ⟨word_linear (hbnum.trans (by omega)) hp hℓ,word_linear (by omega) hp hℓ⟩

theorem sourceScalar_abs (C : Enclosures p S hm) : |C.sourceScalar|≤1 := by
  have ha0 : (0 : ℚ)≤alpha p S hm := by exact_mod_cast (alpha_pos p S hm).le
  have ha1 : alpha p S hm≤1 := by exact_mod_cast (spacing_bounds p S hm).2.2.1
  have hlo := C.mode_lower_ge_one
  have hmid : C.mode.lo≤C.mode.midpoint := by
    dsimp [Maxwell.Certificate.Interval.midpoint]
    linarith only [C.mode.ordered]
  have hm1 : (1 : ℚ)≤C.mode.midpoint := hlo.trans hmid
  change |alpha p S hm/C.mode.midpoint|≤1
  rw [abs_of_nonneg (div_nonneg ha0 (zero_le_one.trans hm1)),div_le_one (zero_lt_one.trans_le hm1)]
  exact ha1.trans hm1

theorem sourceAmplitude_abs (C : Enclosures p S hm) (hb : S.source≠0) (i : Fin S.n) :
    |(sourceAmplitude S (sourcePrecision p S) C.sourceScalar i).value|≤2 := by
  have hq : |C.sourceScalar*Maxwell.Logical.Normalization.normalizedSource S i|≤1 := by
    rw [abs_mul]
    exact (mul_le_mul (sourceScalar_abs p S hm C)
      (Maxwell.Logical.Normalization.normalizedSource_bound S hb i) (abs_nonneg _) zero_le_one).trans_eq
      (one_mul 1)
  have he := roundDyadic_error_rat (sourcePrecision p S)
    (C.sourceScalar*Maxwell.Logical.Normalization.normalizedSource S i)
  have hh : (1/2 : ℚ)^(sourcePrecision p S)≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  have ht := abs_sub_le
    (sourceAmplitude S (sourcePrecision p S) C.sourceScalar i).value
    (C.sourceScalar*Maxwell.Logical.Normalization.normalizedSource S i) 0
  rw [sub_zero,sub_zero] at ht
  rw [abs_sub_comm] at he
  change |(sourceAmplitude S (sourcePrecision p S) C.sourceScalar i).value-
    C.sourceScalar*Maxwell.Logical.Normalization.normalizedSource S i|≤_ at he
  exact ht.trans (by linarith only [he,hq,hh])

theorem sourceAmplitude_word_bits (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S))
    (C : Enclosures p S hm) (hb : S.source≠0) (i : Fin S.n) :
    (sourceAmplitude S (sourcePrecision p S) C.sourceScalar i).numeratorBits≤
      scalarWordCoefficient p*logSize S ∧
    Maxwell.unsignedBitLength (2^sourcePrecision p S)≤scalarWordCoefficient p*logSize S := by
  have hv : |(sourceAmplitude S (sourcePrecision p S) C.sourceScalar i).value|≤(2 : ℚ)^1 := by
    simpa only [pow_one] using sourceAmplitude_abs p S hm C hb i
  have hn := dyadic_numerator_bits_of_bound (sourceAmplitude S (sourcePrecision p S) C.sourceScalar i) hv
  have hp := (selected_precisions_linear p S hm hm2 hu).2.2.2.1
  have hℓ := Parameters.inputLog_pos S.nnz
  rw [Maxwell.Dyadic.denominator_bitLength]
  have hh : (outputBitCoefficient p+onsitePrecisionCoefficient p+4)*logSize S =
      scalarWordCoefficient p*logSize S := by
    unfold scalarWordCoefficient
    rw [Nat.add_comm (outputBitCoefficient p) (onsitePrecisionCoefficient p)]
  exact ⟨(word_linear (by simpa only [Nat.add_assoc] using hn) hp hℓ).trans_eq hh,
    (word_linear (by omega) hp hℓ).trans_eq hh⟩

#print axioms wellStrength_word_bits
#print axioms sourceAmplitude_word_bits

end Maxwell.Continuum.RealizationParameters
