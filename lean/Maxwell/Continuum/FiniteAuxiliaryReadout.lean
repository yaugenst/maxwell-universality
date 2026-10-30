import Maxwell.Continuum.FiniteAuxiliarySourceSchur
import Maxwell.Continuum.FiniteAuxiliaryNorms

/-! Actual ideal observable moments. The maps use the translated physical
source templates, and their stability bound is independent of the number
of disjoint wells. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass

attribute [local irreducible] Auxiliary.resolvent realMode Sh Qh

variable {ι : Type*} [Fintype ι]

def idealReadout (h : ℝ) (r : ι → Space) (v : ι → ℝ) (u : FieldL2) :
    FieldL2 →L[ℂ] BrightSpace ι :=
  (brightCoefficient u).comp ((diagonal v).comp (collection h r))

omit [Fintype ι] in
theorem idealReadout_apply (h : ℝ) (r : ι → Space) (v : ι → ℝ) (u f : FieldL2) (i : ι) :
    idealReadout h r v u f i = (v i : ℂ)*inner ℂ (siteInsertion h (r i) u) f := by
  change inner ℂ u ((v i : ℂ) • siteRestriction h (r i) f) = _
  rw [inner_smul_right, ← siteRestriction_adjoint, ContinuousLinearMap.adjoint_inner_left]

theorem idealReadout_norm {h V : ℝ} (hh : 0 < h) (hV : 0 ≤ V)
    (r : ι → Space) (v : ι → ℝ) (hv : ∀ i, |v i| ≤ V)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) h⁻¹) (Metric.ball (r j) h⁻¹))
    (u : FieldL2) (hu : ‖u‖ = 1) : ‖idealReadout h r v u‖ ≤ V := by
  have hc := collection_norm hh r hdisj
  have hd := diagonal_norm_le v hV hv
  have hp := brightCoefficient_norm_le (ι := ι) u hu
  calc
    _ ≤ ‖brightCoefficient (ι := ι) u‖*(‖diagonal v‖*‖collection h r‖) :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1*(V*1) := mul_le_mul hp
      (mul_le_mul hd hc (norm_nonneg _) hV) (by positivity) zero_le_one
    _ = V := by ring

theorem idealReadout_stability {h V : ℝ} (hh : 0 < h) (hV : 0 ≤ V)
    (r : ι → Space) (v : ι → ℝ) (hv : ∀ i, |v i| ≤ V)
    (hdisj : Pairwise fun i j => Disjoint (Metric.ball (r i) h⁻¹) (Metric.ball (r j) h⁻¹))
    (u : FieldL2) (hu : ‖u‖ = 1) (f g : FieldL2) :
    ‖idealReadout h r v u f-idealReadout h r v u g‖ ≤ V*‖f-g‖ := by
  rw [← map_sub]
  exact (idealReadout h r v u).le_of_opNorm_le (idealReadout_norm hh hV r v hv hdisj u hu) _

theorem idealReadout_auxiliaryField {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64)
    (r : ι → Space) (v : ι → ℝ) (hv : ∀ i, v i ≠ 0)
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι)
    (hA : (A : DefectSpace ι →L[ℂ] DefectSpace ι) = auxiliaryMatrix D hσ0 hσ r v)
    (f : FieldL2) :
    idealReadout h r v (realMode D hh) (auxiliaryField D hσ0 hσ r A f) =
      brightResponse D hh hσ0 hσ r A f := by
  change brightCoefficient (realMode D hh)
    (diagonal v (collection h r (auxiliaryField D hσ0 hσ r A f))) = _
  rw [← defectResponse_eq D hσ0 hσ r v hv A hA f]
  rfl

#print axioms idealReadout_apply
#print axioms idealReadout_stability
#print axioms idealReadout_auxiliaryField

end Maxwell.Continuum.FiniteAuxiliary
