import Maxwell.Continuum.ContinuumDecoderResources
import Maxwell.Continuum.ContinuumDescription

/-! The decoder description and its entire ambient-grid message stream are
included in the continuum representation and bit-cost estimates. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

namespace Maxwell.Continuum.RealizationParameters
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude
  MasterConstants.exponent computedEnclosures

def decoderDescriptionCoefficient (p : Source.Parameters) : ℝ :=
  32*(Parameters.sourceRecordCoefficient p+1)*(decoderWordCoefficient p+1)

def decoderMessageCoefficient (p : Source.Parameters) : ℝ :=
  8*Parameters.sourceVolumeCoefficient p*outputBitCoefficient p

def decoderCostCoefficient (p : Source.Parameters) : ℝ :=
  46080000*(decoderDescriptionCoefficient p+decoderMessageCoefficient p+1)*
    (decoderWordCoefficient p+1)^2

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

theorem decoder_description_polynomial (hm2 : 2≤S.nnz) (hp : Source.Promises p S) (hb : S.source≠0) :
    ((FiniteDecoder.description (decoder p S hm)).length : ℝ)≤decoderDescriptionCoefficient p*
      (S.nnz : ℝ)^(3/2 : ℝ)*(logSize S : ℝ)^3 := by
  have hℓ : (1 : ℝ)≤logSize S := by exact_mod_cast Parameters.inputLog_pos S.nnz
  have hn : (S.n : ℝ)+1≤(Parameters.sourceRecordCoefficient p+1)*
      (S.nnz : ℝ)^(3/2 : ℝ)*(logSize S : ℝ)^2 := by
    have hd : (S.n : ℝ)+1≤(sites p S hm : ℝ)+1 := by
      exact_mod_cast Nat.add_le_add_right (dimension_le_sites p S hm) 1
    exact hd.trans (sites_plus_one_polynomial p S hm hm2 hp.1)
  have hn0 : 0≤(Parameters.sourceRecordCoefficient p+1)*
      (S.nnz : ℝ)^(3/2 : ℝ)*(logSize S : ℝ)^2 :=
    (by positivity : 0≤(S.n : ℝ)+1).trans hn
  have hB : (decoderWordCoefficient p : ℝ)*(logSize S : ℝ)+1≤
      (decoderWordCoefficient p+1)*(logSize S : ℝ) := by nlinarith only [hℓ]
  have hh : ((FiniteDecoder.description (decoder p S hm)).length : ℝ)≤
      32*((S.n : ℝ)+1)*((decoderWordCoefficient p : ℝ)*(logSize S : ℝ)+1) := by
    exact_mod_cast decoder_description_length p S hm hm2 hp hb
  calc
    _≤32*((Parameters.sourceRecordCoefficient p+1)*(S.nnz : ℝ)^(3/2 : ℝ)*(logSize S : ℝ)^2)*
        ((decoderWordCoefficient p+1)*(logSize S : ℝ)) := hh.trans (by gcongr)
    _=_ := by unfold decoderDescriptionCoefficient; ring

theorem decoder_messages_polynomial (hm2 : 2≤S.nnz) (hu : IsUnit (Source.realMatrix S)) :
    ((gridCount p S hm*(decoder p S hm).format.width : ℕ) : ℝ)≤decoderMessageCoefficient p*
      (S.nnz : ℝ)^(3/2 : ℝ)*(logSize S : ℝ)^25 := by
  have hg : (gridCount p S hm : ℝ)≤8*((ambientCells p S hm).length : ℝ) := by
    exact_mod_cast gridCount_ambient p S hm
  have hv := Parameters.source_physical_volume_bound p S hm hm2 hu
  rw [← ambientCells_volume p S hm] at hv
  have hw : ((decoder p S hm).format.width : ℝ)≤(outputBitCoefficient p : ℝ)*(logSize S : ℝ) := by
    exact_mod_cast decoder_format_width p S hm hm2 hu
  rw [Nat.cast_mul]
  calc
    _≤(8*(Parameters.sourceVolumeCoefficient p*(S.nnz : ℝ)^(3/2 : ℝ)*(logSize S : ℝ)^24))*
        ((outputBitCoefficient p : ℝ)*(logSize S : ℝ)) := by
      apply mul_le_mul (hg.trans (mul_le_mul_of_nonneg_left hv (by norm_num))) hw (by positivity)
      exact (Nat.cast_nonneg _).trans (hg.trans (mul_le_mul_of_nonneg_left hv (by norm_num)))
    _=_ := by unfold decoderMessageCoefficient; ring

def completeDescriptionBits (j : Fin (drawCount p S hm)) : List Bool :=
  descriptionBits p S hm j++FiniteDecoder.description (decoder p S hm)

def completeDescriptionCoefficient (p : Source.Parameters) : ℝ :=
  descriptionBitCoefficient p+decoderDescriptionCoefficient p

theorem completeDescriptionBits_polynomial (hm2 : 2≤S.nnz) (hp : Source.Promises p S)
    (hb : S.source≠0) (j : Fin (drawCount p S hm)) :
    ((completeDescriptionBits p S hm j).length : ℝ)≤completeDescriptionCoefficient p*
      (S.nnz : ℝ)^(3/2 : ℝ)*(logSize S : ℝ)^64 := by
  have hℓ : (1 : ℝ)≤logSize S := by exact_mod_cast Parameters.inputLog_pos S.nnz
  have hC : 0≤decoderDescriptionCoefficient p := by
    unfold decoderDescriptionCoefficient
    have := Parameters.sourceRecordCoefficient_nonneg p
    positivity
  have hd := (decoder_description_polynomial p S hm hm2 hp hb).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hℓ (by decide : 3≤64))
      (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
  have hh := add_le_add (descriptionBits_polynomial p S hm hm2 hp hb j) hd
  simp only [completeDescriptionBits,List.length_append,Nat.cast_add]
  exact hh.trans_eq (by unfold completeDescriptionCoefficient;ring)

theorem decoder_cost_polynomial (hm2 : 2≤S.nnz) (hp : Source.Promises p S) (hb : S.source≠0) :
    (FiniteDecoder.costCap (decoder p S hm) : ℝ)≤decoderCostCoefficient p*
      (S.nnz : ℝ)^(3/2 : ℝ)*(logSize S : ℝ)^27 := by
  have hℓ : (1 : ℝ)≤logSize S := by exact_mod_cast Parameters.inputLog_pos S.nnz
  have hmp : (1 : ℝ)≤(S.nnz : ℝ)^(3/2 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hm) (by norm_num)
  have hC : 0≤decoderDescriptionCoefficient p := by
    unfold decoderDescriptionCoefficient
    have := Parameters.sourceRecordCoefficient_nonneg p
    positivity
  have hd := (decoder_description_polynomial p S hm hm2 hp hb).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hℓ (by decide : 3≤25))
      (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
  have hmsgs := decoder_messages_polynomial p S hm hm2 hp.1
  have h1 := one_le_mul_of_one_le_of_one_le hmp (one_le_pow₀ hℓ (n := 25))
  have hsum : ((FiniteDecoder.description (decoder p S hm)).length : ℝ)+
      (gridCount p S hm : ℝ)*(decoder p S hm).format.width+1≤
      (decoderDescriptionCoefficient p+decoderMessageCoefficient p+1)*
        (S.nnz : ℝ)^(3/2 : ℝ)*(logSize S : ℝ)^25 := by
    rw [Nat.cast_mul] at hmsgs
    have h := add_le_add (add_le_add hd hmsgs) h1
    exact h.trans_eq (by ring)
  have hsum0 : 0≤(decoderDescriptionCoefficient p+decoderMessageCoefficient p+1)*
      (S.nnz : ℝ)^(3/2 : ℝ)*(logSize S : ℝ)^25 :=
    (by positivity : 0≤((FiniteDecoder.description (decoder p S hm)).length : ℝ)+
      (gridCount p S hm : ℝ)*(decoder p S hm).format.width+1).trans hsum
  have hB : (decoderWordCoefficient p : ℝ)*(logSize S : ℝ)+1≤
      (decoderWordCoefficient p+1)*(logSize S : ℝ) := by nlinarith only [hℓ]
  have hc : (FiniteDecoder.costCap (decoder p S hm) : ℝ)≤
      46080000*(((FiniteDecoder.description (decoder p S hm)).length : ℝ)+
        (gridCount p S hm : ℝ)*(decoder p S hm).format.width+1)*
        ((decoderWordCoefficient p : ℝ)*(logSize S : ℝ)+1)^2 := by
    exact_mod_cast decoder_cost p S hm hm2 hp hb
  calc
    _≤46080000*((decoderDescriptionCoefficient p+decoderMessageCoefficient p+1)*
        (S.nnz : ℝ)^(3/2 : ℝ)*(logSize S : ℝ)^25)*
        ((decoderWordCoefficient p+1)*(logSize S : ℝ))^2 := hc.trans (by gcongr)
    _=_ := by unfold decoderCostCoefficient; ring

#print axioms completeDescriptionBits_polynomial
#print axioms decoder_cost_polynomial

end Maxwell.Continuum.RealizationParameters
