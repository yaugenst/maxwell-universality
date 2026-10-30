import Maxwell.Continuum.FiniteAuxiliaryOperator
import Maxwell.Continuum.FiniteAuxiliaryCoordinates

/-! The auxiliary physical source and field, and the exact inverse of
the source equation I-WR. All maps are literal continuum L² operators. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass

attribute [local irreducible] Auxiliary.resolvent Qh

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem diagonal_inv_cancel (v : ι → ℝ) (hv : ∀ i, v i ≠ 0) (f : DefectSpace ι) :
    diagonal v (diagonal (fun i => (v i)⁻¹) f) = f := by
  apply PiLp.ext
  intro i
  simp only [diagonal_apply, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (hv i),
    Complex.ofReal_one, one_smul]

omit [Fintype ι] in
theorem diagonal_inv_cancel' (v : ι → ℝ) (hv : ∀ i, v i ≠ 0) (f : DefectSpace ι) :
    diagonal (fun i => (v i)⁻¹) (diagonal v f) = f := by
  apply PiLp.ext
  intro i
  simp only [diagonal_apply, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ (hv i),
    Complex.ofReal_one, one_smul]

def defectResponse {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (r : ι → Space)
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι) (f : FieldL2) : DefectSpace ι :=
  A.symm (collection h r (resolvent D hσ0 hσ f))

def auxiliarySource {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (r : ι → Space)
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι) (f : FieldL2) : FieldL2 :=
  f+insertion h r (defectResponse D hσ0 hσ r A f)

def auxiliaryField {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (r : ι → Space)
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι) (f : FieldL2) : FieldL2 :=
  resolvent D hσ0 hσ (auxiliarySource D hσ0 hσ r A f)

theorem defectResponse_equation {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (r : ι → Space) (v : ι → ℝ)
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι)
    (hA : (A : DefectSpace ι →L[ℂ] DefectSpace ι) = auxiliaryMatrix D hσ0 hσ r v)
    (f : FieldL2) :
    diagonal (fun i => (v i)⁻¹) (defectResponse D hσ0 hσ r A f) =
      collection h r (auxiliaryField D hσ0 hσ r A f) := by
  have he := A.apply_symm_apply (collection h r (resolvent D hσ0 hσ f))
  change (A : DefectSpace ι →L[ℂ] DefectSpace ι) (defectResponse D hσ0 hσ r A f) = _ at he
  rw [hA] at he
  change diagonal (fun i => (v i)⁻¹) (defectResponse D hσ0 hσ r A f)-
    collection h r (resolvent D hσ0 hσ ((collection h r).adjoint (defectResponse D hσ0 hσ r A f))) = _ at he
  rw [collection_adjoint] at he
  change _ = collection h r (resolvent D hσ0 hσ (f+insertion h r (defectResponse D hσ0 hσ r A f)))
  rw [map_add, map_add]
  exact sub_eq_iff_eq_add.mp he

theorem defectResponse_eq {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (r : ι → Space) (v : ι → ℝ) (hv : ∀ i, v i ≠ 0)
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι)
    (hA : (A : DefectSpace ι →L[ℂ] DefectSpace ι) = auxiliaryMatrix D hσ0 hσ r v)
    (f : FieldL2) :
    defectResponse D hσ0 hσ r A f = diagonal v (collection h r (auxiliaryField D hσ0 hσ r A f)) := by
  rw [← defectResponse_equation D hσ0 hσ r v A hA f, diagonal_inv_cancel v hv]

theorem auxiliarySource_equation {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (r : ι → Space) (v : ι → ℝ) (hv : ∀ i, v i ≠ 0)
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι)
    (hA : (A : DefectSpace ι →L[ℂ] DefectSpace ι) = auxiliaryMatrix D hσ0 hσ r v)
    (f : FieldL2) :
    auxiliarySource D hσ0 hσ r A f = f+finiteWellOperator h r v (auxiliaryField D hσ0 hσ r A f) := by
  rw [auxiliarySource, defectResponse_eq D hσ0 hσ r v hv A hA f]
  have he := congrArg (fun T : FieldL2 →L[ℂ] FieldL2 => T (auxiliaryField D hσ0 hσ r A f))
    (collection_weighted_square h r v)
  rw [collection_adjoint] at he
  exact congrArg (fun u => f+u) he

def sourceEquation {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (r : ι → Space) (v : ι → ℝ) : FieldL2 →L[ℂ] FieldL2 :=
  1-(finiteWellOperator h r v).comp (resolvent D hσ0 hσ)

def sourceInverse {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (r : ι → Space)
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι) : FieldL2 →L[ℂ] FieldL2 :=
  1+(insertion h r).comp ((A.symm : DefectSpace ι →L[ℂ] DefectSpace ι).comp
    ((collection h r).comp (resolvent D hσ0 hσ)))

theorem sourceInverse_apply {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (r : ι → Space)
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι) (f : FieldL2) :
    sourceInverse D hσ0 hσ r A f = auxiliarySource D hσ0 hσ r A f := rfl

theorem sourceInverse_right {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (r : ι → Space) (v : ι → ℝ) (hv : ∀ i, v i ≠ 0)
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι)
    (hA : (A : DefectSpace ι →L[ℂ] DefectSpace ι) = auxiliaryMatrix D hσ0 hσ r v) :
    (sourceEquation D hσ0 hσ r v).comp (sourceInverse D hσ0 hσ r A) = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  change auxiliarySource D hσ0 hσ r A f-
    finiteWellOperator h r v (auxiliaryField D hσ0 hσ r A f) = f
  rw [auxiliarySource_equation D hσ0 hσ r v hv A hA f, add_sub_cancel_right]

theorem sourceInverse_left {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (r : ι → Space) (v : ι → ℝ) (hv : ∀ i, v i ≠ 0)
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι)
    (hA : (A : DefectSpace ι →L[ℂ] DefectSpace ι) = auxiliaryMatrix D hσ0 hσ r v) :
    (sourceInverse D hσ0 hσ r A).comp (sourceEquation D hσ0 hσ r v) = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  have hw : finiteWellOperator h r v (resolvent D hσ0 hσ f) =
      insertion h r (diagonal v (collection h r (resolvent D hσ0 hσ f))) := by
    simpa only [collection_adjoint, ContinuousLinearMap.comp_apply] using
      (congrArg (fun T : FieldL2 →L[ℂ] FieldL2 => T (resolvent D hσ0 hσ f))
        (collection_weighted_square h r v)).symm
  have hr : defectResponse D hσ0 hσ r A (sourceEquation D hσ0 hσ r v f) =
      diagonal v (collection h r (resolvent D hσ0 hσ f)) := by
    apply A.injective
    rw [defectResponse, A.apply_symm_apply]
    change _ = (A : DefectSpace ι →L[ℂ] DefectSpace ι) _
    rw [hA]
    change collection h r (resolvent D hσ0 hσ (f-finiteWellOperator h r v (resolvent D hσ0 hσ f))) =
      diagonal (fun i => (v i)⁻¹) (diagonal v (collection h r (resolvent D hσ0 hσ f)))-
        collection h r (resolvent D hσ0 hσ ((collection h r).adjoint
          (diagonal v (collection h r (resolvent D hσ0 hσ f)))))
    rw [diagonal_inv_cancel' v hv, collection_adjoint, hw, map_sub, map_sub]
  change sourceEquation D hσ0 hσ r v f+
    insertion h r (defectResponse D hσ0 hσ r A (sourceEquation D hσ0 hσ r v f)) = f
  rw [hr]
  change f-finiteWellOperator h r v (resolvent D hσ0 hσ f)+_ = f
  rw [hw, sub_add_cancel]

#print axioms auxiliarySource_equation
#print axioms sourceInverse_left
#print axioms sourceInverse_right

end Maxwell.Continuum.FiniteAuxiliary
