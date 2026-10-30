import Maxwell.Continuum.FiniteAuxiliaryReadout
import Maxwell.Continuum.FiniteAuxiliaryIdealSource

/-! A common even lattice translation inserts the assembled wells into
the PEC box without changing their auxiliary matrix or bright readout. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass Bloch CellGauge FourierSobolev

attribute [local irreducible] Auxiliary.resolvent realMode Sh muH Qh

theorem siteRestriction_shift (h : ℝ) (r a : Space) :
    siteRestriction h (r+a) = (siteRestriction h r).comp (translationOperator a) := by
  rw [siteRestriction, siteRestriction, ← translationOperator_add, ContinuousLinearMap.comp_assoc]

theorem siteInsertion_shift (h : ℝ) (r a : Space) :
    siteInsertion h (r+a) = (translationOperator (-a)).comp (siteInsertion h r) := by
  rw [← siteRestriction_adjoint, siteRestriction_shift, ContinuousLinearMap.adjoint_comp,
    translationOperator_adjoint, siteRestriction_adjoint]

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem collection_shift (h : ℝ) (r : ι → Space) (a : Space) :
    collection h (fun i => r i+a) = (collection h r).comp (translationOperator a) := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro i
  exact congrArg (fun T : FieldL2 →L[ℂ] FieldL2 => T f) (siteRestriction_shift h (r i) a)

theorem insertion_shift (h : ℝ) (r : ι → Space) (a : Space) :
    insertion h (fun i => r i+a) = (translationOperator (-a)).comp (insertion h r) := by
  rw [← collection_adjoint, collection_shift, ContinuousLinearMap.adjoint_comp,
    translationOperator_adjoint, collection_adjoint]

theorem compressed_common_lattice_shift {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (r : ι → Space) (a : Alias) :
    compressed h (fun i => r i+latticeShift a) (resolvent D hσ0 hσ) =
      compressed h r (resolvent D hσ0 hσ) := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [compressed, collection_adjoint]
  rw [collection_shift, insertion_shift]
  simp only [ContinuousLinearMap.comp_apply, translationOperator_apply]
  rw [resolvent_lattice_translation, fieldTranslation_neg_apply]

theorem auxiliaryMatrix_common_lattice_shift {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (r : ι → Space) (v : ι → ℝ) (a : Alias) :
    auxiliaryMatrix D hσ0 hσ (fun i => r i+latticeShift a) v =
      auxiliaryMatrix D hσ0 hσ r v := by
  rw [auxiliaryMatrix, auxiliaryMatrix, compressed_common_lattice_shift]

theorem idealSource_shift {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024)
    (r : ι → Space) (α : ℝ) (g : BrightSpace ι) (a : Space) :
    idealSource D hh (fun i => r i+a) α g = fieldTranslation (-a) (idealSource D hh r α g) := by
  rw [idealSource_eq, idealSource_eq, insertion_shift, ContinuousLinearMap.comp_apply,
    translationOperator_apply, map_smul]

omit [Fintype ι] in
theorem defectResponse_common_lattice_shift {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (r : ι → Space) (a : Alias)
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι) (f : FieldL2) :
    defectResponse D hσ0 hσ (fun i => r i+latticeShift a) A (fieldTranslation (-latticeShift a) f) =
      defectResponse D hσ0 hσ r A f := by
  rw [defectResponse, defectResponse, collection_shift, ContinuousLinearMap.comp_apply,
    translationOperator_apply, resolvent_lattice_translation, fieldTranslation_neg_apply]

theorem auxiliarySource_common_lattice_shift {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (r : ι → Space) (a : Alias)
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι) (f : FieldL2) :
    auxiliarySource D hσ0 hσ (fun i => r i+latticeShift a) A (fieldTranslation (-latticeShift a) f) =
      fieldTranslation (-latticeShift a) (auxiliarySource D hσ0 hσ r A f) := by
  rw [auxiliarySource, auxiliarySource, defectResponse_common_lattice_shift, insertion_shift,
    ContinuousLinearMap.comp_apply, translationOperator_apply, map_add]

theorem auxiliaryField_common_lattice_shift {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (r : ι → Space) (a : Alias)
    (A : DefectSpace ι ≃L[ℂ] DefectSpace ι) (f : FieldL2) :
    auxiliaryField D hσ0 hσ (fun i => r i+latticeShift a) A (fieldTranslation (-latticeShift a) f) =
      fieldTranslation (-latticeShift a) (auxiliaryField D hσ0 hσ r A f) := by
  rw [auxiliaryField, auxiliaryField, auxiliarySource_common_lattice_shift, resolvent_lattice_translation]

omit [Fintype ι] in
theorem idealReadout_shift (h : ℝ) (r : ι → Space) (v : ι → ℝ) (u f : FieldL2) (a : Space) :
    idealReadout h (fun i => r i+a) v u (fieldTranslation (-a) f) = idealReadout h r v u f := by
  simp only [idealReadout, ContinuousLinearMap.comp_apply, collection_shift,
    translationOperator_apply, fieldTranslation_neg_apply]

#print axioms auxiliaryMatrix_common_lattice_shift
#print axioms auxiliaryField_common_lattice_shift

end Maxwell.Continuum.FiniteAuxiliary
