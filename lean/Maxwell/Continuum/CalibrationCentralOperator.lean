import Maxwell.Continuum.CalibrationRationalMatrix
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Exact norm and adjoint transport through the actual orthonormal
24-mode coordinates used by the rational calibration matrix. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Calibration

theorem centralFinOperator_norm (A : centralSpace →L[ℂ] centralSpace) :
    ‖centralFinOperator A‖ = ‖A‖ := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound (centralFinOperator A) (norm_nonneg A) ?_
    intro x
    change ‖centralFinUnitary.symm (A (centralFinUnitary x))‖ ≤ _
    rw [LinearIsometryEquiv.norm_map]
    exact (A.le_opNorm _).trans_eq (by rw [LinearIsometryEquiv.norm_map])
  · refine ContinuousLinearMap.opNorm_le_bound A (norm_nonneg (centralFinOperator A)) ?_
    intro u
    have h := (centralFinOperator A).le_opNorm (centralFinUnitary.symm u)
    change ‖centralFinUnitary.symm (A (centralFinUnitary (centralFinUnitary.symm u)))‖ ≤ _ at h
    simpa only [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.norm_map] using h

theorem centralFinOperator_sub (A B : centralSpace →L[ℂ] centralSpace) :
    centralFinOperator (A-B) = centralFinOperator A-centralFinOperator B := by
  apply ContinuousLinearMap.ext
  intro x
  change centralFinUnitary.symm ((A-B) (centralFinUnitary x)) =
    centralFinUnitary.symm (A (centralFinUnitary x))-centralFinUnitary.symm (B (centralFinUnitary x))
  exact map_sub _ _ _

theorem centralFinOperator_adjoint (A : centralSpace →L[ℂ] centralSpace) :
    (centralFinOperator A).adjoint = centralFinOperator A.adjoint := by
  change ((centralFinUnitary.symm : centralSpace →L[ℂ] EuclideanSpace ℂ (Fin 24)).comp
    (A.comp (centralFinUnitary : EuclideanSpace ℂ (Fin 24) →L[ℂ] centralSpace))).adjoint = _
  simp only [ContinuousLinearMap.adjoint_comp, LinearIsometryEquiv.adjoint_eq_symm,
    LinearIsometryEquiv.symm_symm, ContinuousLinearMap.comp_assoc]
  rfl

theorem centralFinOperator_selfAdjoint (A : centralSpace →L[ℂ] centralSpace)
    (hA : A.IsSymmetric) : (centralFinOperator A).adjoint = centralFinOperator A := by
  rw [centralFinOperator_adjoint]
  congr 1
  exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA

#print axioms centralFinOperator_norm
#print axioms centralFinOperator_selfAdjoint

end Maxwell.Continuum.Calibration
