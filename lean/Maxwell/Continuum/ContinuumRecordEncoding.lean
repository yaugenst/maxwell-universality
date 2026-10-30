import Maxwell.Continuum.ContinuumAmbientEncoding
import Maxwell.Continuum.ContinuumScalarResources
import Maxwell.Continuum.ContinuumRealizationTemplatesCertified
import Maxwell.Continuum.ContinuumCalibrationEnclosures
import Maxwell.Continuum.ParameterRecords

/-! Literal finite well, source, and volume-test records. The common profiles
and test arrays are copied in full at every site in this conservative format.
These are representation bounds; actual generation is charged separately. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

namespace Maxwell.Continuum.RealizationParameters

open Maxwell.Composition FiniteAuxiliary
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude
  MasterConstants.exponent Calibration.FiniteAlgorithm.mode
  computedEnclosures computedModeInterval computedCouplingInterval strengthData

def dyadicBits {P : ℕ} (d : Maxwell.Dyadic P) : List Bool :=
  Maxwell.Codec.nat P++Maxwell.Codec.int d.numerator

private theorem dyadicBits_linear {P C ℓ : ℕ} (d : Maxwell.Dyadic P)
    (_hℓ : 0<ℓ) (hn : d.numeratorBits≤C*ℓ) (hp : P+1≤C*ℓ) :
    (dyadicBits d).length≤(4*C+1)*ℓ := by
  have hu : Maxwell.unsignedBitLength P≤P := by
    rw [Maxwell.Codec.unsignedBitLength_eq_size]
    exact Nat.size_le.mpr (Nat.lt_two_pow_self (n := P))
  simp only [dyadicBits,List.length_append,Maxwell.Codec.nat_length,Maxwell.Codec.int_length]
  change Maxwell.signedBitLength d.numerator≤_ at hn
  nlinarith only [hu,hn,hp,_hℓ]

def materialProfileBitCoefficient (p : Source.Parameters) : ℕ :=
  2^41*(outputBitCoefficient p+1)^3

def recordBitCoefficient (p : Source.Parameters) : ℕ :=
  8*analysisBits p+4*scalarWordCoefficient p+20+
    materialProfileBitCoefficient p+selectedTemplateBitCoefficient p

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

def placementBits (i : SourceDecoration.Vertex S (precision p S hm)) : List Bool :=
  Maxwell.Codec.int (integerCenter p S hm i 0)++Maxwell.Codec.int (integerCenter p S hm i 1)++
    Maxwell.Codec.int (integerCenter p S hm i 2)++Maxwell.Codec.nat (length p S hm)

theorem length_word_bits (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    Maxwell.unsignedBitLength (length p S hm)≤(analysisBits p+1)*logSize S := by
  have hl : length p S hm≤Parameters.sourcePhysicalLengths p S hm 0 := by
    unfold Parameters.sourcePhysicalLengths Parameters.sourceBox
    change length p S hm≤2*(_+length p S hm+_+4)
    omega
  exact (Maxwell.Codec.unsignedBitLength_mono hl).trans (physical_side_word_bits p S hm hm2 hu 0)

theorem placementBits_length (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S))
    (i : SourceDecoration.Vertex S (precision p S hm)) :
    (placementBits p S hm i).length≤(8*analysisBits p+17)*logSize S := by
  have hx := integerCenter_word_bits p S hm hm2 hu i 0
  have hy := integerCenter_word_bits p S hm hm2 hu i 1
  have hz := integerCenter_word_bits p S hm hm2 hu i 2
  have hl := length_word_bits p S hm hm2 hu
  have hℓ := Parameters.inputLog_pos S.nnz
  simp only [placementBits,List.length_append,Maxwell.Codec.int_length,Maxwell.Codec.nat_length]
  nlinarith only [hx,hy,hz,hl,hℓ]

include hm in
theorem materialProfileBits_polynomial (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    (Profile.profileBits (materialPrecision p S)).length≤materialProfileBitCoefficient p*(logSize S)^3 := by
  have hn := (selected_precisions_linear p S hm hm2 hu).2.2.1
  have hℓ := Parameters.inputLog_pos S.nnz
  have hn' : materialPrecision p S+1≤(outputBitCoefficient p+1)*logSize S := by
    nlinarith only [hn,hℓ]
  calc
    _≤2^41*(materialPrecision p S+1)^3 := Profile.profileBits_length _
    _≤2^41*((outputBitCoefficient p+1)*logSize S)^3 := by gcongr
    _=_ := by unfold materialProfileBitCoefficient; ring

def wellBits (i : SourceDecoration.Vertex S (precision p S hm)) : List Bool :=
  placementBits p S hm i++
    dyadicBits (strengthData p S hm (computedEnclosures p S hm).mode (computedEnclosures p S hm).coupling i)++
    Profile.profileBits (materialPrecision p S)++selectedTemplateBits p S hm

def sourceRecordBits (i : Fin S.n) : List Bool :=
  placementBits p S hm (sourceInputSite S (precision p S hm) i)++
    dyadicBits (sourceAmplitude S (sourcePrecision p S) (computedEnclosures p S hm).sourceScalar i)++
    selectedTemplateBits p S hm

theorem wellBits_length (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S)) (hb : S.source≠0)
    (i : SourceDecoration.Vertex S (precision p S hm)) :
    (wellBits p S hm i).length≤recordBitCoefficient p*(logSize S)^25 := by
  have hg := placementBits_length p S hm hm2 hu i
  have hs := wellStrength_word_bits p S hm hm2 hu (computedEnclosures p S hm) hb i
  rw [Maxwell.Dyadic.denominator_bitLength] at hs
  have hd := dyadicBits_linear
    (strengthData p S hm (computedEnclosures p S hm).mode (computedEnclosures p S hm).coupling i)
    (Parameters.inputLog_pos S.nnz) hs.1 hs.2
  have hp := materialProfileBits_polynomial p S hm hm2 hu
  have ht := selectedTemplateBits_bound p S hm hm2 hu
  have hℓ := Parameters.inputLog_pos S.nnz
  change 0<logSize S at hℓ
  change (dyadicBits _).length≤(4*scalarWordCoefficient p+1)*logSize S at hd
  have hl25 : logSize S≤(logSize S)^25 := le_self_pow₀ (by omega) (by decide : (25 : ℕ)≠0)
  have h325 : (logSize S)^3≤(logSize S)^25 := Nat.pow_le_pow_right hℓ (by decide)
  have hg' := hg.trans (Nat.mul_le_mul_left _ hl25)
  have hd' := hd.trans (Nat.mul_le_mul_left _ hl25)
  have hp' := hp.trans (Nat.mul_le_mul_left _ h325)
  have hc : (8*analysisBits p+17)+(4*scalarWordCoefficient p+1)+
      materialProfileBitCoefficient p+selectedTemplateBitCoefficient p≤recordBitCoefficient p := by
    unfold recordBitCoefficient
    omega
  have hsum := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hg' hd') hp') ht
  have hcost := Nat.mul_le_mul_right ((logSize S)^25) hc
  simp only [Nat.add_mul] at hcost hsum
  simp only [wellBits,List.length_append]
  exact hsum.trans hcost

theorem sourceRecordBits_length (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S))
    (hb : S.source≠0) (i : Fin S.n) :
    (sourceRecordBits p S hm i).length≤recordBitCoefficient p*(logSize S)^25 := by
  have hg := placementBits_length p S hm hm2 hu (sourceInputSite S (precision p S hm) i)
  have hs := sourceAmplitude_word_bits p S hm hm2 hu (computedEnclosures p S hm) hb i
  rw [Maxwell.Dyadic.denominator_bitLength] at hs
  have hd := dyadicBits_linear _ (Parameters.inputLog_pos S.nnz) hs.1 hs.2
  have ht := selectedTemplateBits_bound p S hm hm2 hu
  have hℓ := Parameters.inputLog_pos S.nnz
  change 0<logSize S at hℓ
  change (dyadicBits _).length≤(4*scalarWordCoefficient p+1)*logSize S at hd
  have hl25 : logSize S≤(logSize S)^25 := le_self_pow₀ (by omega) (by decide : (25 : ℕ)≠0)
  have hg' := hg.trans (Nat.mul_le_mul_left _ hl25)
  have hd' := hd.trans (Nat.mul_le_mul_left _ hl25)
  simp only [sourceRecordBits,List.length_append]
  unfold recordBitCoefficient
  nlinarith only [hg',hd',ht,Nat.zero_le (materialProfileBitCoefficient p*(logSize S)^25)]

def wellStream : List Bool :=
  Maxwell.Codec.list (wellBits p S hm) (Finset.univ : Finset (SourceDecoration.Vertex S (precision p S hm))).toList

def sourceStream : List Bool := Maxwell.Codec.list (sourceRecordBits p S hm) (List.finRange S.n)

private theorem list_length_polynomial {α : Type*} (xs : List α) (f : α→List Bool) (C ℓ : ℕ)
    (hℓ : 0<ℓ) (hf : ∀x∈xs,(f x).length≤C*ℓ^25) :
    (Maxwell.Codec.list f xs).length≤(xs.length+1)*(C+3)*ℓ^25 := by
  have h := Maxwell.Codec.list_length_le f xs (C*ℓ^25) hf
  have hu : Maxwell.unsignedBitLength xs.length≤xs.length := by
    rw [Maxwell.Codec.unsignedBitLength_eq_size]
    exact Nat.size_le.mpr (Nat.lt_two_pow_self (n := xs.length))
  have hp : 1≤ℓ^25 := one_le_pow₀ (by omega)
  nlinarith only [h,hu,hp,Nat.zero_le (C*ℓ^25)]

theorem wellStream_length (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S)) (hb : S.source≠0) :
    (wellStream p S hm).length≤(sites p S hm+1)*(recordBitCoefficient p+3)*(logSize S)^25 := by
  have h := list_length_polynomial
    (Finset.univ : Finset (SourceDecoration.Vertex S (precision p S hm))).toList
    (wellBits p S hm) (recordBitCoefficient p) (logSize S) (Parameters.inputLog_pos S.nnz)
    (fun i _ => wellBits_length p S hm hm2 hu hb i)
  simpa only [wellStream,sites,Finset.length_toList,Finset.card_univ] using h

theorem sourceStream_length (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S)) (hb : S.source≠0) :
    (sourceStream p S hm).length≤(S.n+1)*(recordBitCoefficient p+3)*(logSize S)^25 := by
  simpa only [sourceStream,List.length_finRange] using
    list_length_polynomial (List.finRange S.n) (sourceRecordBits p S hm)
      (recordBitCoefficient p) (logSize S) (Parameters.inputLog_pos S.nnz)
      (fun i _ => sourceRecordBits_length p S hm hm2 hu hb i)

#print axioms wellBits_length
#print axioms sourceRecordBits_length
#print axioms wellStream_length
#print axioms sourceStream_length

end Maxwell.Continuum.RealizationParameters
