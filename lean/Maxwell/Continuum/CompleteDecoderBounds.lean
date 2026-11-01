import Maxwell.Continuum.CompleteDecoder
import Maxwell.Continuum.ContinuumDescriptionParseCost
import Maxwell.Continuum.Main
import Maxwell.Codec.OutputWidth

/-! Quantitative execution of the complete continuum decoder, including the
physical description, for every finite message pattern and every draw. -/

noncomputable section
namespace Maxwell.Continuum.CompleteDecoder
open RealizationParameters Maxwell.Cost.DecoderParser
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
attribute [local irreducible] Parameters.sourceInput Parameters.sourceMagnitude
  MasterConstants.exponent computedEnclosures

def outputCoefficient (p : Source.Parameters) : ℕ :=
  4*decoderWordCoefficient p+3*outputBitCoefficient p+7

def costCoefficient (p : Source.Parameters) : ℝ :=
  DescriptionSchema.parseCoefficient p+decoderCostCoefficient p+5

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

theorem output_width (hm2 : 2≤S.nnz) (hp : Source.Promises p S) (hb : S.source≠0) :
    decoderWidth (decoder p S hm)+2≤outputCoefficient p*logSize S := by
  have hw := decoder_words p S hm hm2 hp hb
  have hd := decoderWidth_bound (decoder p S hm) (decoderWordCoefficient p*logSize S) 1
    hw.offset (fun i q _ => hw.weight i q) (fun i => (decoder_support p S hm i).le)
  have hf := decoder_format_width p S hm hm2 hp.1
  have hℓ : 0<logSize S := Parameters.inputLog_pos S.nnz
  unfold outputCoefficient
  nlinarith only [hd,hf,hℓ]

theorem cost_polynomial (hm2 : 2≤S.nnz) (hp : Source.Promises p S) (hb : S.source≠0)
    (j : Fin (drawCount p S hm)) :
    ((computedCost (DescriptionSchema.data p S hm j) (decoder p S hm)+1 : ℕ):ℝ)≤
      costCoefficient p*(S.nnz:ℝ)^(3/2:ℝ)*(logSize S:ℝ)^89 := by
  have hparse := DescriptionSchema.parse_cost_polynomial p S hm hm2 hp hb j
  have hdecode := decoder_cost_polynomial p S hm hm2 hp hb
  have hℓ : (1:ℝ)≤logSize S := by exact_mod_cast Parameters.inputLog_pos S.nnz
  have hm1 : (1:ℝ)≤(S.nnz:ℝ)^(3/2:ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hm) (by norm_num)
  have hC : 0≤decoderCostCoefficient p*(S.nnz:ℝ)^(3/2:ℝ) := by
    have hc : 0≤decoderCostCoefficient p := by
      unfold decoderCostCoefficient decoderDescriptionCoefficient decoderMessageCoefficient
        Parameters.sourceVolumeCoefficient
      have := Parameters.sourceRecordCoefficient_nonneg p
      have := Parameters.routingVolumeCoefficient_nonneg p
      positivity
    exact mul_nonneg hc (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hdecode' := hdecode.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hℓ (by decide : 27≤89)) hC)
  have h1 := one_le_mul_of_one_le_of_one_le hm1 (one_le_pow₀ hℓ (n:=89))
  simp only [computedCost,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
  unfold costCoefficient
  nlinarith only [hparse,hdecode',h1]

theorem decodes (C : Realization.Constants) (hm2 : 2≤S.nnz) (hp : Source.Promises p S)
    (hb : S.source≠0) (hC : outputCoefficient p≤C.wordCoefficient)
    (j : Fin (drawCount p S hm)) :
    Realization.Decodes program (Realization.computedBytes p S hm j) (decoder p S hm)
      (Realization.wordBudget C S) (computedCost (DescriptionSchema.data p S hm j) (decoder p S hm)+1) := by
  intro w
  obtain ⟨stop,he,ho,hr⟩ := computed_run (DescriptionSchema.data p S hm j)
    (decoder p S hm) w (fun _ => false)
  refine ⟨stop,?_,ho.mono ((output_width p S hm hm2 hp hb).trans
    (Nat.mul_le_mul_right _ hC)),hr⟩
  simpa only [Realization.computedBytes,completeDescriptionBits,DescriptionSchema.data_wire,
    List.cons_append,List.append_assoc] using he

#print axioms output_width
#print axioms cost_polynomial
#print axioms decodes

end Maxwell.Continuum.CompleteDecoder
