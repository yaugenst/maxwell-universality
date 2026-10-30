import Maxwell.Continuum.BoxReferenceField
import Maxwell.Continuum.BoxBoundaryEstimate
import Maxwell.Continuum.BoxCutoffLocalization
import Maxwell.Continuum.SchwartzMaterial
import Maxwell.Continuum.MomentumLeakageResidual

/-! The finite PEC reference field solves the literal assembled
dielectric equation up to the proved bulk leakage and boundary terms. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.BoxCutoff

open Auxiliary FourierSobolev SchwartzMultiplier BoxModes CellGauge EffectiveMass MasterConstants Bloch

attribute [local irreducible] Auxiliary.resolvent actualSource cutoffOperator Cs

variable {ι : Type*} [Fintype ι]

def referenceResidual {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (N : Fin 3 → ℝ)
    (r : ι → Space) (v : ι → ℝ) {f : FieldL2} (Df : H1Data f) (g : FieldL2) : FieldL2 :=
  (pecCurlCurl (boxDomain N) (referenceDomain D hσ0 hσ N Df) : FieldL2)-
    PeriodicMaterial.dielectric.multiplier (referenceField D hσ0 hσ N f)-
    ((z+σ : ℝ) : ℂ) • (referenceField D hσ0 hσ N f : FieldL2)-
    finiteWellOperator h r v (referenceField D hσ0 hσ N f)-g

theorem reference_residual_identity {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (N : Fin 3 → ℝ)
    (r : ι → Space) (v : ι → ℝ) {f : FieldL2} (Df : H1Data f) (g : FieldL2)
    (heq : f = g+finiteWellOperator h r v (resolvent D hσ0 hσ f))
    (hg : field (schwartz N) g = g) :
    referenceResidual D hσ0 hσ N r v Df g =
      field (schwartz N) (cutoffOperator f-f)+
        curlCurlCommutator (schwartz N) (resolventH1 D hσ0 hσ Df) := by
  have hcut : field (schwartz N) f = g+
      finiteWellOperator h r v (field (schwartz N) (resolvent D hσ0 hσ f)) := by
    have hc := congrArg (field (schwartz N)) heq
    rw [map_add, hg, field_commutes_wells] at hc
    exact hc
  rw [referenceResidual, reference_action]
  change field (schwartz N) (resolventImage D hσ0 hσ f)+
    curlCurlCommutator (schwartz N) (resolventH1 D hσ0 hσ Df)-
    PeriodicMaterial.dielectric.multiplier (field (schwartz N) (resolvent D hσ0 hσ f))-
    ((z+σ : ℝ) : ℂ) • field (schwartz N) (resolvent D hσ0 hσ f)-
    finiteWellOperator h r v (field (schwartz N) (resolvent D hσ0 hσ f))-g = _
  rw [resolventImage, map_add, map_add, map_smul, field_commutes_dielectric, map_sub, hcut]
  abel

theorem reference_residual_norm {L z σ b : ℝ} (hL : Ls ≤ L) (D : Calibration L⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4/64) (n : Fin 3 → ℕ) (hb : 0 ≤ b)
    (r : ι → Space) (v : ι → ℝ) (hv0 : ∀ i, 0 ≤ v i) (hv : ∀ i, v i ≤ (2 : ℝ)^130*(L⁻¹)^2)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) L) (Metric.ball (r j) L))
    {f : FieldL2} (Df : H1Data f) (c : ι → ℂ)
    (heq : f = (∑ i, c i • fieldTranslation (-r i) (actualSource D (inverse_length_le_1024 hL)))+
      finiteWellOperator L⁻¹ r v (resolvent D hσ0 hσ f))
    (hf : familyProjection (interiorCells n b) f = f)
    (hdf : ∀ j, familyProjection (interiorCells n b) (Df.derivative j) = Df.derivative j)
    (hg : familyProjection (interiorCells n b)
      (∑ i, c i • fieldTranslation (-r i) (actualSource D (inverse_length_le_1024 hL))) =
      ∑ i, c i • fieldTranslation (-r i) (actualSource D (inverse_length_le_1024 hL))) :
    ‖referenceResidual D hσ0 hσ (side n) r v Df
      (∑ i, c i • fieldTranslation (-r i) (actualSource D (inverse_length_le_1024 hL)))‖ ≤
      Cs*(1+(Fintype.card ι : ℝ))*Real.exp (-cs*L^(1/3 : ℝ))*(‖f‖+∑ i, ‖c i‖)+
        (2 : ℝ)^26*boundaryCellMajorant L b (∏ j, (n j : ℝ))*Df.norm := by
  rw [reference_residual_identity D hσ0 hσ _ r v Df _ heq (cutoff_preserves_source n hb _ hg)]
  apply (norm_add_le _ _).trans
  apply add_le_add _ (cutoff_resolvent_commutator hL D hσ0 hσ n Df hf hdf)
  apply ((field_norm_le zero_le_one _ (schwartz_norm (side n)) _).trans_eq (one_mul _)).trans
  rw [norm_sub_rev]
  exact nestedMomentumLeakage hL D hσ0 hσ r v hv0 hv hdisj f c heq

#print axioms reference_residual_norm

end Maxwell.Continuum.BoxCutoff
