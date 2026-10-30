import Maxwell.Continuum.AuxiliaryTranslationBounds

/-! The actual local inverse before insertion of the smooth cutoff. Its
zero extension is only a bookkeeping map on Bloch L²; on the cutoff region
it is the full maximal-domain Maxwell inverse. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Auxiliary

open FreeFiber PeriodicBand FiberAnalytic Bloch MeasureTheory

attribute [local irreducible] fiberResolvent cutoffFiber Auxiliary.resolvent Bloch.unitary

def localInverseFiber (z σ : ℝ) : QuasiCell → FiberMap :=
  cutoffRegion.indicator (fun q => fiberResolvent z σ (fun j => q.val j))

theorem localInverseFiber_eq {z σ : ℝ} {q : QuasiCell} (hq : q ∈ cutoffRegion) :
    localInverseFiber z σ q = fiberResolvent z σ (fun j => q.val j) :=
  Set.indicator_of_mem hq _

theorem localInverseFiber_zero {z σ : ℝ} {q : QuasiCell} (hq : q ∉ cutoffRegion) :
    localInverseFiber z σ q = 0 := Set.indicator_of_notMem hq _

theorem localInverseFiber_measurable {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) :
    AEStronglyMeasurable (localInverseFiber z σ) quasiMeasure := by
  apply (aestronglyMeasurable_indicator_iff cutoffRegion_isOpen.measurableSet).mpr
  apply ContinuousOn.aestronglyMeasurable _ cutoffRegion_isOpen.measurableSet
  intro q hq
  have hq' : ‖realMomentum (fun j => q.val j)‖ ≤ 4 * smallRadius :=
    (show ‖quasiMomentum q‖ < 4 * smallRadius from hq).le
  have hp : ContinuousAt (fun p : QuasiCell => fun j => p.val j) q :=
    (continuous_pi fun j => (PiLp.continuous_apply 2 _ j).comp continuous_subtype_val).continuousAt
  exact ((fiberResolvent_continuousAt D hσ0 hσ _ hq').comp hp).continuousWithinAt

theorem localInverseFiber_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (q : QuasiCell) :
    ‖localInverseFiber z σ q‖ ≤ 4 * (h^2)⁻¹ := by
  by_cases hq : q ∈ cutoffRegion
  · rw [localInverseFiber_eq hq]
    exact fiberResolvent_norm_le D hσ0 hσ _
      (show ‖quasiMomentum q‖ ≤ 4 * smallRadius from
        (show ‖quasiMomentum q‖ < 4 * smallRadius from hq).le)
  · rw [localInverseFiber_zero hq, norm_zero]
    positivity

def localInverseData {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) :
    FiberMultiplier.Data (H := FiberSpace) quasiMeasure (4*(h^2)⁻¹) where
  operator := localInverseFiber z σ
  measurable := localInverseFiber_measurable D hσ0 hσ
  nonneg := by positivity
  bound := localInverseFiber_norm_le D hσ0 hσ

def localInverse {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) : FieldL2 →L[ℂ] FieldL2 :=
  physicalize (localInverseData D hσ0 hσ).multiplier

theorem localInverse_ae {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (f : FieldL2) :
    unitary (localInverse D hσ0 hσ f) =ᵐ[quasiMeasure]
      fun q => localInverseFiber z σ q (unitary f q) := by
  rw [localInverse, unitary_physicalize]
  exact (localInverseData D hσ0 hσ).multiplier_ae _

theorem localInverse_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) :
    ‖localInverse D hσ0 hσ‖ ≤ 4*(h^2)⁻¹ :=
  physicalize_norm_le _ (by positivity) (localInverseData D hσ0 hσ).multiplier_norm_le

theorem cutoffFiber_eq_local (z σ : ℝ) (q : QuasiCell) :
    cutoffFiber z σ q = (cutoff q.val : ℂ) • localInverseFiber z σ q := by
  by_cases hq : q ∈ cutoffRegion
  · rw [cutoffFiber_eq hq, localInverseFiber_eq hq]
  · rw [cutoffFiber_zero hq, localInverseFiber_zero hq]
    apply ContinuousLinearMap.ext
    intro u
    change (0 : FiberSpace) = (cutoff q.val : ℂ) • (0 : FiberSpace)
    exact (smul_zero (cutoff q.val : ℂ)).symm

theorem resolvent_eq_local_cutoff {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) :
    resolvent D hσ0 hσ = localInverse D hσ0 hσ * cutoffOperator := by
  apply ContinuousLinearMap.ext
  intro f
  apply unitary.injective
  apply Lp.ext
  filter_upwards [resolvent_ae D hσ0 hσ f,
    localInverse_ae D hσ0 hσ (cutoffOperator f), cutoffOperator_ae f] with q hr hl hc
  change unitary (resolvent D hσ0 hσ f) q = unitary (localInverse D hσ0 hσ (cutoffOperator f)) q
  rw [hr, hl, hc, map_smul, cutoffFiber_eq_local, smul_apply]

theorem resolvent_eq_cutoff_local {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) :
    resolvent D hσ0 hσ = cutoffOperator * localInverse D hσ0 hσ := by
  apply ContinuousLinearMap.ext
  intro f
  apply unitary.injective
  apply Lp.ext
  filter_upwards [resolvent_ae D hσ0 hσ f,
    cutoffOperator_ae (localInverse D hσ0 hσ f), localInverse_ae D hσ0 hσ f] with q hr hc hl
  change unitary (resolvent D hσ0 hσ f) q = unitary (cutoffOperator (localInverse D hσ0 hσ f)) q
  rw [hr, hc, hl, cutoffFiber_eq_local, smul_apply]

theorem resolventTranslationCommutator_identity {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (a : Space) :
    resolventTranslationCommutator D hσ0 hσ a =
      localInverse D hσ0 hσ * PeriodicMaterial.translationCommutator a * resolvent D hσ0 hσ := by
  apply ContinuousLinearMap.ext
  intro f
  apply unitary.injective
  apply Lp.ext
  filter_upwards [unitary_resolventTranslationCommutator_ae D hσ0 hσ a f,
    localInverse_ae D hσ0 hσ (PeriodicMaterial.translationCommutator a (resolvent D hσ0 hσ f)),
    unitary_translationCommutator_ae a (resolvent D hσ0 hσ f),
    resolvent_ae D hσ0 hσ f] with q hr hl hc hf
  change unitary (resolventTranslationCommutator D hσ0 hσ a f) q =
    unitary (localInverse D hσ0 hσ (PeriodicMaterial.translationCommutator a (resolvent D hσ0 hσ f))) q
  rw [hr, hl, hc, hf]
  by_cases hq : q ∈ cutoffRegion
  · rw [localInverseFiber_eq hq]
    exact cutoffFiber_translation_identity D hσ0 hσ a q hq _
  · rw [localInverseFiber_zero hq, cutoffFiber_zero hq]
    simp

#print axioms resolvent_eq_local_cutoff
#print axioms resolventTranslationCommutator_identity

end Maxwell.Continuum.Auxiliary
