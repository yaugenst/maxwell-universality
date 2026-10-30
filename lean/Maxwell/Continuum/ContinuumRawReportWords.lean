import Maxwell.Continuum.ContinuumRawReports

/-! Every fixed-width report pattern has bounded arithmetic output, including
patterns which fail the physical accuracy test. Canonical reduction can only
decrease the explicitly bounded dyadic numerator and denominator. -/

namespace Maxwell.Continuum.RationalWords
open Maxwell.Cost.RationalAccumulator

theorem width_dyadic {P B : ℕ} (d : Maxwell.Dyadic P)
    (hn : d.numeratorBits≤B) (hd : Maxwell.unsignedBitLength (2^P)≤B) : Width d.value B := by
  have hn' : d.numerator.natAbs.bits.length≤B := by
    simp only [Maxwell.Dyadic.numeratorBits,Maxwell.signedBitLength,
      Maxwell.Codec.unsignedBitLength_eq_size,← Nat.size_eq_bits_len] at hn
    omega
  have hd' : (2^P).bits.length≤B := by
    simpa only [Maxwell.Codec.unsignedBitLength_eq_size,← Nat.size_eq_bits_len] using hd
  have he : d.value=(d.numerator : ℚ)/(2^P : ℕ) := by
    simp only [Maxwell.Dyadic.value,Nat.cast_pow,Nat.cast_ofNat]
  rw [he]
  exact ⟨(bits_mono (reduced_numerator d.numerator (2^P) (by positivity))).trans hn',
    (bits_mono (reduced_denominator d.numerator (2^P) (by positivity))).trans hd'⟩

end Maxwell.Continuum.RationalWords

namespace Maxwell.Continuum.FiniteAuxiliary

theorem momentWordDyadic_numerator_bits (P B : ℕ) (w : Fin (2^(B+1))) :
    (momentWordDyadic P B w).numeratorBits≤B+2 := by
  have hw : (w.val : ℤ)<(2 : ℤ)^(B+1) := by exact_mod_cast w.isLt
  rw [pow_succ (2 : ℤ) B] at hw
  have h0 : (0 : ℤ)≤w.val := Int.natCast_nonneg _
  have hn : |(w.val : ℤ)-(2 : ℤ)^B|≤(2 : ℤ)^B := abs_le.mpr ⟨by omega,by omega⟩
  have hn' : ((w.val : ℤ)-(2 : ℤ)^B).natAbs≤2^B := by
    rw [← Int.natCast_natAbs] at hn
    exact_mod_cast hn
  have hb := Maxwell.Codec.unsignedBitLength_mono hn'
  rw [Maxwell.Dyadic.denominator_bitLength] at hb
  change Maxwell.unsignedBitLength ((w.val : ℤ)-(2 : ℤ)^B).natAbs+1≤_
  omega

end Maxwell.Continuum.FiniteAuxiliary

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

namespace Maxwell.Continuum.RealizationParameters

open Maxwell.Composition FiniteAuxiliary RationalWords
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude
  MasterConstants.exponent computedEnclosures strengthData

def decodedWordCoefficient (p : Source.Parameters) : ℕ :=
  normalizationWordCoefficient p+scalarWordCoefficient p+outputBitCoefficient p+1

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

theorem rawReportDyadic_width (hm2 : 2≤S.nnz) (huS : IsUnit (Source.realMatrix S))
    (w : RawReportWord p S hm) :
    Width (rawReportDyadic p S hm w).value ((outputBitCoefficient p+1)*logSize S) := by
  have hs := selected_precisions_linear p S hm hm2 huS
  have hℓ := Parameters.inputLog_pos S.nnz
  change 0<logSize S at hℓ
  have hn := momentWordDyadic_numerator_bits (momentPrecision p S)
    (messageRangeBits (inverseBound p S hm) S.nnz+momentPrecision p S+2) w
  have hw := hs.2.2.2.2.2.2.2
  have hP := hs.2.2.2.2.1
  apply width_dyadic
  · change (momentWordDyadic _ _ w).numeratorBits≤_
    nlinarith only [hn,hw,hℓ]
  · rw [Maxwell.Dyadic.denominator_bitLength]
    nlinarith only [hP,hℓ]

theorem wellStrength_width (hm2 : 2≤S.nnz) (huS : IsUnit (Source.realMatrix S))
    (C : Enclosures p S hm) (hb : S.source≠0)
    (i : SourceDecoration.Vertex S (precision p S hm)) :
    Width (C.wellStrength i) (scalarWordCoefficient p*logSize S) := by
  have h := wellStrength_word_bits p S hm hm2 huS C hb i
  exact width_dyadic (strengthData p S hm C.mode C.coupling i) h.1 h.2

theorem weightedRawReports_width (hm2 : 2≤S.nnz) (huS : IsUnit (Source.realMatrix S))
    (C : Enclosures p S hm) (hb : S.source≠0)
    (w : SourceDecoration.Vertex S (precision p S hm) → RawReportWord p S hm)
    (i : SourceDecoration.Vertex S (precision p S hm)) :
    Width (weightedRawReports p S hm C w i)
      ((scalarWordCoefficient p+outputBitCoefficient p+1)*logSize S) := by
  have h := (wellStrength_width p S hm hm2 huS C hb i).mul
    (rawReportDyadic_width p S hm hm2 huS (w i))
  simpa only [weightedRawReports,Nat.add_mul,Nat.add_assoc] using h

theorem decodeRawReports_width (hm2 : 2≤S.nnz) (hp : Source.Promises p S) (hb : S.source≠0)
    (w : SourceDecoration.Vertex S (precision p S hm) → RawReportWord p S hm) (i : Fin S.n) :
    Width (decodeRawReports p S hm w i) (decodedWordCoefficient p*logSize S) := by
  have h := (normalizationScale_width p S hm hp).mul
    (weightedRawReports_width p S hm hm2 hp.1 (computedEnclosures p S hm) hb w
      (Sum.inl (SourceRouting.inputCoordinate S (precision p S hm) i)))
  simpa only [decodeRawReports,sparseMomentDecode,PositiveRecovery.decode,normalizationScale,
    decodedWordCoefficient,Nat.add_mul,Nat.add_assoc] using h

theorem decodeRawReports_word_bits (hm2 : 2≤S.nnz) (hp : Source.Promises p S) (hb : S.source≠0)
    (w : SourceDecoration.Vertex S (precision p S hm) → RawReportWord p S hm) (i : Fin S.n) :
    Maxwell.rationalBitLength (decodeRawReports p S hm w i)≤
      (2*decodedWordCoefficient p+1)*logSize S := by
  have h := decodeRawReports_width p S hm hm2 hp hb w i
  have hℓ := Parameters.inputLog_pos S.nnz
  change 0<logSize S at hℓ
  simp only [Maxwell.rationalBitLength,Maxwell.signedBitLength,
    Maxwell.Codec.unsignedBitLength_eq_size,← Nat.size_eq_bits_len]
  nlinarith only [h.num,h.den,hℓ]

#print axioms rawReportDyadic_width
#print axioms decodeRawReports_width
#print axioms decodeRawReports_word_bits

end Maxwell.Continuum.RealizationParameters
