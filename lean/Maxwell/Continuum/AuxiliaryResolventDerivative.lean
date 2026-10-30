import Maxwell.Continuum.AuxiliaryDerivativeResolvent
import Maxwell.Continuum.PeriodicMaterialCommutatorDerivative
import Maxwell.Continuum.FourierTranslationCharacterization

/-! The actual weak spatial derivative identity for the full cutoff
Maxwell resolvent, on every H¹ source. Domain membership follows from
the translation limit; no common-domain premise is required. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Auxiliary

open Bloch FourierSobolev Filter MeasureTheory
open scoped Topology

attribute [local irreducible] Auxiliary.resolvent localInverse derivativeResolvent

theorem inverse_real_smul (t : ℝ) (f : FieldL2) : (t : ℂ)⁻¹ • f = t⁻¹ • f := by
  rw [← Complex.ofReal_inv]
  exact IsScalarTower.algebraMap_smul ℂ (t⁻¹ : ℝ) f

theorem resolvent_quotient_identity {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (j : Fin 3) (t : ℝ) (f : FieldL2) :
    t⁻¹ • (fieldTranslation (t • coordinateDirection j) (resolvent D hσ0 hσ f) -
      resolvent D hσ0 hσ f) =
      resolvent D hσ0 hσ (t⁻¹ • (fieldTranslation (t • coordinateDirection j) f-f)) +
      localInverse D hσ0 hσ ((t : ℂ)⁻¹ •
        PeriodicMaterial.translationCommutator (t • coordinateDirection j) (resolvent D hσ0 hσ f)) := by
  rw [← inverse_real_smul, ← inverse_real_smul, map_smul, map_smul, ← smul_add]
  apply congrArg (fun u : FieldL2 => (t : ℂ)⁻¹ • u)
  have hc := congrArg (fun T : FieldL2 →L[ℂ] FieldL2 => T f)
    (resolventTranslationCommutator_identity D hσ0 hσ (t • coordinateDirection j))
  change fieldTranslation (t • coordinateDirection j) (resolvent D hσ0 hσ f) -
      resolvent D hσ0 hσ (fieldTranslation (t • coordinateDirection j) f) =
    localInverse D hσ0 hσ (PeriodicMaterial.translationCommutator
      (t • coordinateDirection j) (resolvent D hσ0 hσ f)) at hc
  rw [← hc, map_sub]
  abel

theorem resolvent_translation_hasDerivAt {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) {f : FieldL2} (Df : H1Data f) (j : Fin 3) :
    HasDerivAt (fun t : ℝ => fieldTranslation (t • coordinateDirection j) (resolvent D hσ0 hσ f))
      (resolvent D hσ0 hσ (Df.derivative j) + derivativeResolvent D hσ0 hσ j f) 0 := by
  have hs := (Df.translation_hasDerivAt j).tendsto_slope_zero
  simp only [zero_add, zero_smul, fieldTranslation_zero] at hs
  have hr := (resolvent D hσ0 hσ).continuous.continuousAt.tendsto.comp hs
  have hc := (localInverse D hσ0 hσ).continuous.continuousAt.tendsto.comp
    (PeriodicMaterial.materialCommutatorQuotient_tendsto j (resolvent D hσ0 hσ f))
  have ht := hr.add hc
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simp only [zero_add, zero_smul, fieldTranslation_zero]
  have he (t : ℝ) := resolvent_quotient_identity D hσ0 hσ j t f
  simpa only [Function.comp_def, ← he, derivativeResolvent, mul_apply_eq_comp] using ht

/-- Actual H¹ data for the cutoff-resolvent output. -/
def resolventH1 {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) {f : FieldL2} (Df : H1Data f) :
    H1Data (resolvent D hσ0 hσ f) where
  derivative j := resolvent D hσ0 hσ (Df.derivative j) + derivativeResolvent D hσ0 hσ j f
  weak_derivative j := fieldWeakDerivative_of_translation_hasDerivAt j _ _
    (resolvent_translation_hasDerivAt D hσ0 hσ Df j)

theorem resolvent_weak_derivative {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) {f : FieldL2} (Df : H1Data f) (j k : Fin 3) :
    partialDistribution j (Lp.toTemperedDistribution (resolvent D hσ0 hσ f k)) =
      Lp.toTemperedDistribution
        ((resolvent D hσ0 hσ (Df.derivative j) + derivativeResolvent D hσ0 hσ j f) k) :=
  (resolventH1 D hσ0 hσ Df).weak_derivative j k

#print axioms resolvent_translation_hasDerivAt
#print axioms resolvent_weak_derivative

end Maxwell.Continuum.Auxiliary
