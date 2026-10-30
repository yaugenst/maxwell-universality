import Maxwell.Continuum.MomentumLeakage
import Maxwell.Continuum.AuxiliaryResolventGraph

/-! The cutoff leakage is the actual physical distributional residual.
No cutoff is inserted in the assembled dielectric equation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Auxiliary

open Bloch EffectiveMass MasterConstants

attribute [local irreducible] Auxiliary.resolvent actualSource cutoffOperator fieldDistribution

variable {ι : Type*} [Fintype ι]

theorem assembled_distribution_residual {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (r : ι → Space) (v : ι → ℝ) (f g : FieldL2)
    (heq : f = g+finiteWellOperator h r v (resolvent D hσ0 hσ f)) :
    curlDistribution (curlDistribution (fieldDistribution (resolvent D hσ0 hσ f))) -
      fieldDistribution (PeriodicMaterial.dielectric.multiplier (resolvent D hσ0 hσ f)) -
      ((z+σ : ℝ) : ℂ) • fieldDistribution (resolvent D hσ0 hσ f) -
      fieldDistribution (finiteWellOperator h r v (resolvent D hσ0 hσ f)) - fieldDistribution g =
      fieldDistribution (cutoffOperator f-f) := by
  rw [resolvent_distribution_identity, map_sub]
  have he := congrArg fieldDistribution heq
  rw [map_add] at he
  rw [he]
  abel

/-- A literal L² residual represents the exact assembled continuum PDE
error and obeys the proved leakage budget. -/
theorem assembled_physical_residual {L z σ : ℝ} (hL : Ls ≤ L) (D : Calibration L⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4/64) (r : ι → Space) (v : ι → ℝ)
    (hv0 : ∀ i, 0 ≤ v i) (hv : ∀ i, v i ≤ (2 : ℝ)^130*(L⁻¹)^2)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) L) (Metric.ball (r j) L))
    (f : FieldL2) (c : ι → ℂ)
    (heq : f = (∑ i, c i • fieldTranslation (-r i) (actualSource D (inverse_length_le_1024 hL))) +
      finiteWellOperator L⁻¹ r v (resolvent D hσ0 hσ f)) :
    ∃ e : FieldL2,
      ‖e‖ ≤ Cs*(1+(Fintype.card ι : ℝ))*Real.exp (-cs*L^(1/3 : ℝ)) * (‖f‖+∑ i, ‖c i‖) ∧
      curlDistribution (curlDistribution (fieldDistribution (resolvent D hσ0 hσ f))) -
        fieldDistribution (PeriodicMaterial.dielectric.multiplier (resolvent D hσ0 hσ f)) -
        ((z+σ : ℝ) : ℂ) • fieldDistribution (resolvent D hσ0 hσ f) -
        fieldDistribution (finiteWellOperator L⁻¹ r v (resolvent D hσ0 hσ f)) -
        fieldDistribution (∑ i, c i • fieldTranslation (-r i)
          (actualSource D (inverse_length_le_1024 hL))) = fieldDistribution e := by
  refine ⟨cutoffOperator f-f, ?_, assembled_distribution_residual D hσ0 hσ r v f _ heq⟩
  rw [norm_sub_rev]
  exact nestedMomentumLeakage hL D hσ0 hσ r v hv0 hv hdisj f c heq

#print axioms assembled_distribution_residual
#print axioms assembled_physical_residual

end Maxwell.Continuum.Auxiliary
