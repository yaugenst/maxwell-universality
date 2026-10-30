import Maxwell.Continuum.FiniteWellMaterial
import Maxwell.Continuum.PeriodicMaterialTranslation

/-! A physical well restriction and its adjoint insertion. Outputs use
coordinates relative to the well center, so the same on-site mode is
inserted at every site. Their product is the literal translated well. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

open MeasureTheory Bloch EffectiveMass Auxiliary
open scoped ComplexOrder

theorem translationOperator_adjoint (r : Space) :
    (translationOperator r).adjoint = translationOperator (-r) := by
  rw [translationOperator, LinearIsometryEquiv.adjoint_eq_symm]
  apply ContinuousLinearMap.ext
  intro f
  apply (fieldTranslation r).injective
  exact ((fieldTranslation r).apply_symm_apply f).trans (fieldTranslation_neg_apply r f).symm

def siteRestriction (h : ℝ) (r : Space) : FieldL2 →L[ℂ] FieldL2 :=
  (Qh h).comp (translationOperator r)

def siteInsertion (h : ℝ) (r : Space) : FieldL2 →L[ℂ] FieldL2 :=
  (translationOperator (-r)).comp (Qh h)

theorem siteRestriction_adjoint (h : ℝ) (r : Space) :
    (siteRestriction h r).adjoint = siteInsertion h r := by
  rw [siteRestriction, ContinuousLinearMap.adjoint_comp, translationOperator_adjoint,
    (Qh_selfAdjoint h).adjoint_eq]
  rfl

theorem siteInsertion_adjoint (h : ℝ) (r : Space) :
    (siteInsertion h r).adjoint = siteRestriction h r := by
  rw [← siteRestriction_adjoint, ContinuousLinearMap.adjoint_adjoint]

theorem siteRestriction_norm (h : ℝ) (r : Space) : ‖siteRestriction h r‖ ≤ 1 := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  exact (mul_le_mul (Qh_norm_le h) (translationOperator_norm_le r)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem siteInsertion_norm (h : ℝ) (r : Space) : ‖siteInsertion h r‖ ≤ 1 := by
  rw [← siteRestriction_adjoint, LinearIsometryEquiv.norm_map]
  exact siteRestriction_norm h r

theorem translatedWell_conjugation (h : ℝ) (r : Space) :
    (translationOperator (-r)).comp ((Wh h).comp (translationOperator r)) = translatedWell h r := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro j
  apply Lp.ext
  have hm := (measurePreserving_add_right volume (-r)).quasiMeasurePreserving.ae_eq_comp
    (Wh_ae h (fieldTranslation r f) j)
  have ht := (measurePreserving_add_right volume (-r)).quasiMeasurePreserving.ae_eq_comp
    (fieldTranslation_ae r f j)
  filter_upwards [fieldTranslation_ae (-r) (Wh h (fieldTranslation r f)) j,
    translatedWell_ae h r f j, hm, ht] with x h₁ h₂ h₃ h₄
  change fieldTranslation (-r) (Wh h (fieldTranslation r f)) j x = translatedWell h r f j x
  dsimp only [Function.comp_apply] at h₃ h₄
  rw [h₁, h₂, h₃, h₄]
  simp only [sub_eq_add_neg, neg_add_cancel_right]

theorem siteInsertion_restriction (h : ℝ) (r : Space) :
    (siteInsertion h r).comp (siteRestriction h r) = translatedWell h r := by
  calc
    _ = (translationOperator (-r)).comp ((Wh h).comp (translationOperator r)) := by
      unfold siteInsertion siteRestriction
      rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc (Qh h),
        show (Qh h).comp (Qh h) = Wh h from Qh_square h]
    _ = _ := translatedWell_conjugation h r

#print axioms siteRestriction_adjoint
#print axioms siteInsertion_restriction

end Maxwell.Continuum.FiniteAuxiliary
