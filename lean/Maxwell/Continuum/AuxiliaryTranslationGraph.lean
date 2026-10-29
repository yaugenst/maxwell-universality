import Maxwell.Continuum.BlochTranslationFiber
import Maxwell.Continuum.AuxiliaryResolventReality

/-! Translation identities for the actual cutoff resolvent, derived from
the maximal fiber graphs and the literal dielectric commutator. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Auxiliary

open FreeFiber PeriodicBand Bloch MeasureTheory

attribute [local irreducible] resolvent cutoffFiber fiberResolvent fiberInverse
  FiberAnalytic.fullResolventExtension scaledBand PeriodicPerturbation.perturbation
  PeriodicPerturbation.finiteK CornerBridge.topState RankOneBand.Data.bandRoot

theorem cutoffOperator_translation (a : Space) (f : FieldL2) :
    fieldTranslation a (cutoffOperator f) = cutoffOperator (fieldTranslation a f) := by
  apply unitary.injective
  apply Lp.ext
  filter_upwards [unitary_fieldTranslation_ae a (cutoffOperator f), cutoffOperator_ae f,
    cutoffOperator_ae (fieldTranslation a f), unitary_fieldTranslation_ae a f]
    with q ht hc hct htf
  rw [ht, hc, hct, htf, map_smul]

theorem cutoffFiber_translation_graph {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64) (a : Space) (q : QuasiCell) (f : FiberSpace) :
    (fiberTranslation a q (cutoffFiber z σ q f) -
      cutoffFiber z σ q (fiberTranslation a q f),
      fiberMaterialCommutator a q (cutoffFiber z σ q f)) ∈
      (materialFiber (quasiMomentum q) (sampledEnergy z σ) backgroundAmplitude).graph := by
  have hg := fiberTranslation_material_graph a q (sampledEnergy z σ) _ _
    (cutoffFiber_graph D hσ0 hσ q f)
  have hs := (materialFiber (quasiMomentum q) (sampledEnergy z σ) backgroundAmplitude).graph.sub_mem
    hg (cutoffFiber_graph D hσ0 hσ q (fiberTranslation a q f))
  change (fiberTranslation a q (cutoffFiber z σ q f) -
      cutoffFiber z σ q (fiberTranslation a q f),
    (fiberTranslation a q ((cutoff q.val : ℂ) • f) +
      fiberMaterialCommutator a q (cutoffFiber z σ q f)) -
      (cutoff q.val : ℂ) • fiberTranslation a q f) ∈ _ at hs
  simpa only [map_smul, add_sub_cancel_left] using hs

theorem cutoffFiber_translation_identity {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64) (a : Space) (q : QuasiCell)
    (hq : q ∈ cutoffRegion) (f : FiberSpace) :
    fiberTranslation a q (cutoffFiber z σ q f) - cutoffFiber z σ q (fiberTranslation a q f) =
      fiberResolvent z σ (fun j => q.val j)
        (fiberMaterialCommutator a q (cutoffFiber z σ q f)) := by
  have hq' : ‖realMomentum (fun j => q.val j)‖ ≤ 4 * smallRadius :=
    (show ‖quasiMomentum q‖ < 4 * smallRadius from hq).le
  have hi := boundedInverse_map_of_graph (fiberInverse D hσ0 hσ _ hq')
    (cutoffFiber_translation_graph D hσ0 hσ a q f)
  rw [← fiberResolvent_eq_inverse D hσ0 hσ _ hq'] at hi
  exact hi.symm

theorem cutoffFiber_translation_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64) (a : Space) (q : QuasiCell) (f : FiberSpace) :
    ‖fiberTranslation a q (cutoffFiber z σ q f) - cutoffFiber z σ q (fiberTranslation a q f)‖ ≤
      (4 * (h ^ 2)⁻¹) * ‖fiberMaterialCommutator a q (cutoffFiber z σ q f)‖ := by
  by_cases hq : q ∈ cutoffRegion
  · rw [cutoffFiber_translation_identity D hσ0 hσ a q hq f]
    exact (fiberResolvent z σ (fun j => q.val j)).le_of_opNorm_le
      (fiberResolvent_norm_le D hσ0 hσ _
        (show ‖realMomentum (fun j => q.val j)‖ ≤ 4 * smallRadius from
          (show ‖quasiMomentum q‖ < 4 * smallRadius from hq).le)) _
  · simp only [cutoffFiber_zero hq, zero_apply, map_zero, sub_zero, norm_zero, mul_zero, le_refl]

def resolventTranslationCommutator {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64) (a : Space) : FieldL2 →L[ℂ] FieldL2 :=
  translationOperator a * resolvent D hσ0 hσ - resolvent D hσ0 hσ * translationOperator a

theorem unitary_resolventTranslationCommutator_ae {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64) (a : Space) (f : FieldL2) :
    unitary (resolventTranslationCommutator D hσ0 hσ a f) =ᵐ[quasiMeasure]
      (fun q => fiberTranslation a q (cutoffFiber z σ q (unitary f q)) -
        cutoffFiber z σ q (fiberTranslation a q (unitary f q))) := by
  change unitary (fieldTranslation a (resolvent D hσ0 hσ f) -
      resolvent D hσ0 hσ (fieldTranslation a f)) =ᵐ[quasiMeasure] _
  rw [map_sub]
  filter_upwards [Lp.coeFn_sub (unitary (fieldTranslation a (resolvent D hσ0 hσ f)))
      (unitary (resolvent D hσ0 hσ (fieldTranslation a f))),
    unitary_fieldTranslation_ae a (resolvent D hσ0 hσ f), resolvent_ae D hσ0 hσ f,
    resolvent_ae D hσ0 hσ (fieldTranslation a f), unitary_fieldTranslation_ae a f]
      with q hs ht hr hrt htf
  rw [hs]
  simp only [Pi.sub_apply]
  rw [ht, hr, hrt, htf]

theorem resolventTranslationCommutator_source_bound {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64) (a : Space) (f : FieldL2) :
    ‖resolventTranslationCommutator D hσ0 hσ a f‖ ≤
      (4 * (h ^ 2)⁻¹) * ‖PeriodicMaterial.translationCommutator a (resolvent D hσ0 hσ f)‖ := by
  rw [← unitary_norm (resolventTranslationCommutator D hσ0 hσ a f),
    ← unitary_norm (PeriodicMaterial.translationCommutator a (resolvent D hσ0 hσ f))]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [unitary_resolventTranslationCommutator_ae D hσ0 hσ a f,
    unitary_translationCommutator_ae a (resolvent D hσ0 hσ f),
    resolvent_ae D hσ0 hσ f] with q hc hε hr
  rw [hc, hε, hr]
  exact cutoffFiber_translation_norm_le D hσ0 hσ a q (unitary f q)

end Maxwell.Continuum.Auxiliary
