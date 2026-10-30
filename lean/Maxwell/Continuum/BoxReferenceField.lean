import Maxwell.Continuum.PECCutoffDomain
import Maxwell.Continuum.BoxCutoffBasic
import Maxwell.Continuum.AuxiliaryResolventGraph
import Maxwell.Continuum.AuxiliaryResolventDerivative

/-! The actual finite-PEC reference field, including its proved
operator-domain membership and exact L² operator image. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.BoxCutoff

open Auxiliary FourierSobolev SchwartzMultiplier BoxModes Bloch

def resolventImage {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (f : FieldL2) : FieldL2 :=
  cutoffOperator f+((z+σ : ℝ) : ℂ) • resolvent D hσ0 hσ f+
    PeriodicMaterial.dielectric.multiplier (resolvent D hσ0 hσ f)

theorem resolvent_image_distribution {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (f : FieldL2) :
    curlDistribution (curlDistribution (fieldDistribution (resolvent D hσ0 hσ f))) =
      fieldDistribution (resolventImage D hσ0 hσ f) := by
  have he := resolvent_periodic_equation D hσ0 hσ f
  unfold WeakPeriodicEquation at he
  rw [resolventImage, map_add]
  exact sub_eq_iff_eq_add.mp he

def referenceField {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (N : Fin 3 → ℝ) (f : FieldL2) : testL2Closure (boxDomain N) :=
  cutoffPhysicalField (boxDomain N) (schwartz N) (schwartz_interior N) (resolvent D hσ0 hσ f)

def referenceImage {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (N : Fin 3 → ℝ) {f : FieldL2} (Df : H1Data f) :
    testL2Closure (boxDomain N) :=
  cutoffPhysicalImage (boxDomain N) (schwartz N) (schwartz_interior N)
    (resolventH1 D hσ0 hσ Df) (resolventImage D hσ0 hσ f)

theorem reference_pec_graph {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (N : Fin 3 → ℝ) {f : FieldL2} (Df : H1Data f) :
    ∃ hu : referenceField D hσ0 hσ N f ∈ (pecCurlCurl (boxDomain N)).domain,
      pecCurlCurl (boxDomain N) ⟨referenceField D hσ0 hσ N f, hu⟩ = referenceImage D hσ0 hσ N Df :=
  cutoff_pecCurlCurl (boxDomain N) (schwartz N) (schwartz_compact N) (schwartz_interior N)
    (resolventH1 D hσ0 hσ Df) (resolvent_image_distribution D hσ0 hσ f)

def referenceDomain {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (N : Fin 3 → ℝ) {f : FieldL2} (Df : H1Data f) :
    (pecCurlCurl (boxDomain N)).domain :=
  ⟨referenceField D hσ0 hσ N f, (reference_pec_graph D hσ0 hσ N Df).choose⟩

theorem reference_action {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (N : Fin 3 → ℝ) {f : FieldL2} (Df : H1Data f) :
    pecCurlCurl (boxDomain N) (referenceDomain D hσ0 hσ N Df) = referenceImage D hσ0 hσ N Df :=
  (reference_pec_graph D hσ0 hσ N Df).choose_spec

theorem reference_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (N : Fin 3 → ℝ) (f : FieldL2) :
    ‖referenceField D hσ0 hσ N f‖ ≤ ‖resolvent D hσ0 hσ f‖ := by
  exact (field_norm_le zero_le_one (schwartz N) (schwartz_norm N) _).trans_eq (one_mul _)

#print axioms reference_pec_graph

end Maxwell.Continuum.BoxCutoff
