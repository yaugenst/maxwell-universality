import Maxwell.Continuum.PeriodicMaterialDifferenceQuotient

/-! The material translation commutator has the literal dielectric
derivative as its strong difference-quotient limit. -/

noncomputable section

namespace Maxwell.Continuum.PeriodicMaterial

open Bloch FourierSobolev Filter
open scoped Topology

theorem derivativeQuotient_translation (j : Fin 3) (t : ℝ) (f : FieldL2) :
    derivativeQuotient j t (fieldTranslation (t • coordinateDirection j) f) =
      (t : ℂ)⁻¹ • translationCommutator (t • coordinateDirection j) f := by
  unfold derivativeQuotient
  change (t : ℂ)⁻¹ • translationCommutator (t • coordinateDirection j)
    (fieldTranslation (-(t • coordinateDirection j)) (fieldTranslation (t • coordinateDirection j) f)) = _
  have he := fieldTranslation_neg_apply (-(t • coordinateDirection j)) f
  rw [neg_neg] at he
  rw [he]

theorem materialCommutatorQuotient_tendsto (j : Fin 3) (f : FieldL2) :
    Tendsto (fun t : ℝ => (t : ℂ)⁻¹ • translationCommutator (t • coordinateDirection j) f)
      (𝓝[≠] 0) (𝓝 (derivativeMultiplier j f)) := by
  have ht : Tendsto (fun t : ℝ => fieldTranslation (t • coordinateDirection j) f)
      (𝓝[≠] 0) (𝓝 f) := by
    have hc : Continuous (fun t : ℝ => fieldTranslation (t • coordinateDirection j) f) :=
      (fieldTranslation_continuous f).comp (continuous_id.smul continuous_const)
    have h0 := hc.tendsto (0 : ℝ)
    simpa only [zero_smul, fieldTranslation_zero] using h0.mono_left nhdsWithin_le_nhds
  have hz : Tendsto (fun t : ℝ => derivativeQuotient j t
      (fieldTranslation (t • coordinateDirection j) f-f)) (𝓝[≠] 0) (𝓝 (0 : FieldL2)) := by
    apply squeeze_zero_norm (fun t => (derivativeQuotient j t).le_of_opNorm_le
      (derivativeQuotient_norm_le j t) _)
    simpa only [sub_self, norm_zero, mul_zero] using
      (ht.sub_const f).norm.const_mul 28
  have hs := (derivativeQuotient_tendsto j f).add hz
  have he (t : ℝ) : derivativeQuotient j t f + derivativeQuotient j t
      (fieldTranslation (t • coordinateDirection j) f-f) =
      (t : ℂ)⁻¹ • translationCommutator (t • coordinateDirection j) f := by
    rw [map_sub, ← derivativeQuotient_translation]
    abel
  simpa only [add_zero, he] using hs

#print axioms materialCommutatorQuotient_tendsto

end Maxwell.Continuum.PeriodicMaterial
