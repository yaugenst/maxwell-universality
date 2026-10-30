import Maxwell.Continuum.ContinuumDecoder
import Maxwell.Continuum.FiniteDecoderWords

/-! The concrete decoder's coefficients, indices and complete message-array
addresses all have logarithmic width. The actual finite program therefore
has near-linear bit cost in the serialized stencil and report stream. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

namespace Maxwell.Continuum.RealizationParameters
open Maxwell.Composition FiniteAuxiliary RationalWords
open Maxwell.Cost Maxwell.Cost.DecoderParser
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude
  MasterConstants.exponent computedEnclosures strengthData momentPrecision messageRangeBits

def decoderWordCoefficient (p : Source.Parameters) : ℕ :=
  3*analysisBits p+normalizationWordCoefficient p+scalarWordCoefficient p+
    2*outputBitCoefficient p+10

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

private theorem bits_le_self (n : ℕ) : n.bits.length≤n := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr (Nat.lt_two_pow_self (n := n))

theorem decoder_format_width (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    (decoder p S hm).format.width≤outputBitCoefficient p*logSize S := by
  have h := (selected_precisions_linear p S hm hm2 hu).2.2.2.2.2.2.2
  change 1+(messageRangeBits (inverseBound p S hm) S.nnz+2)+momentPrecision p S≤_
  omega

theorem decoder_weight_short (hm2 : 2≤S.nnz) (hp : Source.Promises p S) (hb : S.source≠0)
    (i : Fin S.n) (q : Fin (decoder p S hm).sampleCount) :
    Source.ShortRational (↑(decoderWordCoefficient p*logSize S) : ℝ) ((decoder p S hm).weight i q) := by
  have h := (normalizationScale_width p S hm hp).mul
    (wellStrength_width p S hm hm2 hp.1 (computedEnclosures p S hm) hb (readoutSite p S hm i))
  have hℓ := Parameters.inputLog_pos S.nnz
  change 0<logSize S at hℓ
  have hB : normalizationWordCoefficient p*logSize S+scalarWordCoefficient p*logSize S+1≤
      decoderWordCoefficient p*logSize S := by
    unfold decoderWordCoefficient
    nlinarith only [hℓ,Nat.zero_le (analysisBits p),Nat.zero_le (outputBitCoefficient p)]
  constructor
  · change (signedBitLength (normalizationScale S*
      (computedEnclosures p S hm).wellStrength (readoutSite p S hm i)).num : ℝ)≤_
    have hn : signedBitLength (normalizationScale S*
        (computedEnclosures p S hm).wellStrength (readoutSite p S hm i)).num≤
        decoderWordCoefficient p*logSize S := by
      simp only [signedBitLength,Codec.unsignedBitLength_eq_size,← Nat.size_eq_bits_len]
      have hn := h.num
      omega
    exact_mod_cast hn
  · have hd := h.den.trans (show normalizationWordCoefficient p*logSize S+
        scalarWordCoefficient p*logSize S≤decoderWordCoefficient p*logSize S by omega)
    simp only [Codec.unsignedBitLength_eq_size,← Nat.size_eq_bits_len]
    exact_mod_cast hd

structure DecoderWords (B : ℕ) : Prop where
  dimension : S.n.bits.length≤B
  integerBits : (decoder p S hm).format.integerBits.bits.length≤B
  fractionalBits : (decoder p S hm).format.fractionalBits.bits.length≤B
  sampleCount : (decoder p S hm).sampleCount.bits.length≤B
  messageCount : ((decoder p S hm).sampleCount*(decoder p S hm).format.width).bits.length≤B
  format : (decoder p S hm).format.width≤B
  positive : 1≤B
  offset : ∀i,Source.ShortRational B ((decoder p S hm).offset i)
  weight : ∀i q,Source.ShortRational B ((decoder p S hm).weight i q)

theorem decoder_words (hm2 : 2≤S.nnz) (hp : Source.Promises p S) (hb : S.source≠0) :
    DecoderWords p S hm (decoderWordCoefficient p*logSize S) := by
  let B := decoderWordCoefficient p*logSize S
  have hℓ := Parameters.inputLog_pos S.nnz
  change 0<logSize S at hℓ
  have hB : 1≤B := by
    dsimp [B,decoderWordCoefficient]
    nlinarith only [hℓ,Nat.zero_le (analysisBits p),Nat.zero_le (normalizationWordCoefficient p),
      Nat.zero_le (scalarWordCoefficient p),Nat.zero_le (outputBitCoefficient p)]
  have hw := decoder_format_width p S hm hm2 hp.1
  have hJ : (decoder p S hm).sampleCount.bits.length≤(3*analysisBits p+4)*logSize S := by
    simpa only [decoder,Codec.unsignedBitLength_eq_size,← Nat.size_eq_bits_len] using
      gridCount_word_bits p S hm hm2 hp.1
  have hW : (decoder p S hm).format.width≤B := hw.trans (Nat.mul_le_mul_right _ (by
    unfold decoderWordCoefficient
    omega))
  refine ⟨?_,?_,?_,?_,?_,hW,hB,?_,decoder_weight_short p S hm hm2 hp hb⟩
  · have hmB := Codec.unsignedBitLength_mono (Parameters.input_le_binary S.nnz)
    rw [Maxwell.Dyadic.denominator_bitLength] at hmB
    have hn := RationalWords.bits_mono (Source.dimension_le_nnz S hp.1)
    simp only [Codec.unsignedBitLength_eq_size,← Nat.size_eq_bits_len] at hmB
    change S.nnz.bits.length≤logSize S+1 at hmB
    dsimp [B,decoderWordCoefficient]
    nlinarith only [hmB,hn,hℓ,Nat.zero_le (analysisBits p),Nat.zero_le (normalizationWordCoefficient p),
      Nat.zero_le (scalarWordCoefficient p),Nat.zero_le (outputBitCoefficient p)]
  · exact (bits_le_self _).trans ((show (decoder p S hm).format.integerBits≤
      (decoder p S hm).format.width by unfold Target.FixedPointFormat.width;omega).trans hW)
  · exact (bits_le_self _).trans ((show (decoder p S hm).format.fractionalBits≤
      (decoder p S hm).format.width by unfold Target.FixedPointFormat.width;omega).trans hW)
  · exact hJ.trans (Nat.mul_le_mul_right _ (by unfold decoderWordCoefficient;omega))
  · have hmul := RationalAccumulator.bits_mul_le (decoder p S hm).sampleCount (decoder p S hm).format.width
    have hbits := (bits_le_self ((decoder p S hm).format.width)).trans hw
    dsimp [B,decoderWordCoefficient]
    nlinarith only [hmul,hbits,hJ,Nat.zero_le (normalizationWordCoefficient p),
      Nat.zero_le (scalarWordCoefficient p),Nat.zero_le (outputBitCoefficient p),Nat.zero_le (logSize S)]
  · intro i
    have hzero : signedBitLength (0 : ℚ).num=1 ∧ unsignedBitLength (0 : ℚ).den=1 := by decide
    constructor
    · change (signedBitLength (0 : ℚ).num : ℝ)≤_
      rw [hzero.1]
      exact_mod_cast hB
    · change (unsignedBitLength (0 : ℚ).den : ℝ)≤_
      rw [hzero.2]
      exact_mod_cast hB

theorem decoder_description_width (hm2 : 2≤S.nnz) (hp : Source.Promises p S) (hb : S.source≠0) :
    maxWidth FiniteDecoder.descriptionShape (FiniteDecoder.descriptionData (decoder p S hm))≤
      decoderWordCoefficient p*logSize S := by
  have h := decoder_words p S hm hm2 hp hb
  exact FiniteDecoder.description_width (decoder p S hm) _ 1 h.dimension h.integerBits
    h.fractionalBits h.sampleCount (by simpa using h.positive) h.offset
    (fun i q _ => h.weight i q) (fun i => (decoder_support p S hm i).le)

theorem decoder_description_length (hm2 : 2≤S.nnz) (hp : Source.Promises p S) (hb : S.source≠0) :
    (FiniteDecoder.description (decoder p S hm)).length≤
      32*(S.n+1)*(decoderWordCoefficient p*logSize S+1) := by
  have h := decoder_words p S hm hm2 hp hb
  have hh := FiniteDecoder.description_length (decoder p S hm) _ 1 h.dimension h.integerBits
    h.fractionalBits h.sampleCount (by simpa using h.positive) h.offset
    (fun i q _ => h.weight i q) (fun i => (decoder_support p S hm i).le)
  convert hh using 1
  ring

theorem decoder_cost (hm2 : 2≤S.nnz) (hp : Source.Promises p S) (hb : S.source≠0) :
    FiniteDecoder.costCap (decoder p S hm)≤
      46080000*((FiniteDecoder.description (decoder p S hm)).length+
        gridCount p S hm*(decoder p S hm).format.width+1)*
      (decoderWordCoefficient p*logSize S+1)^2 := by
  have h := decoder_words p S hm hm2 hp hb
  have hh := FiniteDecoder.costCap_bounded (decoder p S hm) _ 1
    (decoder_description_width p S hm hm2 hp hb) h.format h.sampleCount h.messageCount h.offset
    (fun i q _ => h.weight i q) (fun i => (decoder_support p S hm i).le)
  rw [show (decoder p S hm).sampleCount=gridCount p S hm from rfl] at hh
  nlinarith only [hh]

#print axioms decoder_words
#print axioms decoder_description_length
#print axioms decoder_cost

end Maxwell.Continuum.RealizationParameters
