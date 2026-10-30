import Maxwell.Continuum.FiniteAuxiliarySite
import Maxwell.Continuum.WellInteractionLattice

/-! Exact lattice covariance of the constructed auxiliary resolvent.
The full infinite-alias translation is one scalar Bloch phase. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

open MeasureTheory Auxiliary EffectiveMass CellGauge Bloch

attribute [local irreducible] Bloch.unitary Auxiliary.resolvent EffectiveMass.Sh

theorem translationOperator_add (r s : Space) :
    (translationOperator r).comp (translationOperator s) = translationOperator (r+s) := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro j
  apply Lp.ext
  have hs := (measurePreserving_add_right volume r).quasiMeasurePreserving.ae_eq_comp
    (fieldTranslation_ae s f j)
  filter_upwards [fieldTranslation_ae r (fieldTranslation s f) j,
    fieldTranslation_ae (r+s) f j, hs] with x ha hb hc
  change fieldTranslation r (fieldTranslation s f) j x = fieldTranslation (r+s) f j x
  dsimp only [Function.comp_apply] at hc
  rw [ha, hc, hb, add_assoc]

theorem latticeShift_neg (a : Bloch.Alias) : latticeShift (-a) = -latticeShift a := by
  apply PiLp.ext
  intro j
  simp only [latticeShift, PiLp.smul_apply, integerVector_apply, Pi.neg_apply,
    Int.cast_neg, PiLp.neg_apply, smul_eq_mul, mul_neg]

theorem latticeShift_sub (a b : Bloch.Alias) : latticeShift (a-b) = latticeShift a-latticeShift b := by
  apply PiLp.ext
  intro j
  simp only [latticeShift, PiLp.smul_apply, integerVector_apply, Pi.sub_apply,
    Int.cast_sub, PiLp.sub_apply, smul_eq_mul, mul_sub]

theorem resolvent_lattice_translation {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (a : Bloch.Alias) (f : FieldL2) :
    resolvent D hσ0 hσ (fieldTranslation (-latticeShift a) f) =
      fieldTranslation (-latticeShift a) (resolvent D hσ0 hσ f) := by
  apply unitary.injective
  apply Lp.ext
  filter_upwards [resolvent_ae D hσ0 hσ (fieldTranslation (-latticeShift a) f),
    unitary_fieldTranslation_ae (-latticeShift a) f,
    unitary_fieldTranslation_ae (-latticeShift a) (resolvent D hσ0 hσ f),
    resolvent_ae D hσ0 hσ f] with q h₁ h₂ h₃ h₄
  rw [h₁, h₂, h₃, h₄, fiberTranslation_lattice, fiberTranslation_lattice, map_smul]

theorem resolvent_lattice_commute {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (a : Bloch.Alias) :
    (translationOperator (latticeShift a)).comp (resolvent D hσ0 hσ) =
      (resolvent D hσ0 hσ).comp (translationOperator (latticeShift a)) := by
  apply ContinuousLinearMap.ext
  intro f
  have he := resolvent_lattice_translation D hσ0 hσ (-a) f
  rw [latticeShift_neg, neg_neg] at he
  exact he.symm

theorem site_interaction_eq {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (a b : Bloch.Alias) :
    (siteRestriction h (latticeShift a)).comp
      ((resolvent D hσ0 hσ).comp (siteInsertion h (latticeShift b))) =
      wellInteraction D hσ0 hσ (b-a) := by
  unfold siteRestriction siteInsertion wellInteraction
  rw [ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc (translationOperator _),
    resolvent_lattice_commute, ContinuousLinearMap.comp_assoc]
  congr 1
  rw [← ContinuousLinearMap.comp_assoc (translationOperator (latticeShift a)), translationOperator_add]
  congr 2
  rw [latticeShift_sub]
  abel

theorem site_interaction_diagonal {h z : ℝ} (D : Calibration h z) (a : Bloch.Alias) :
    (siteRestriction h (latticeShift a)).comp
      ((resolvent D le_rfl (by positivity)).comp (siteInsertion h (latticeShift a))) = Sh D := by
  rw [site_interaction_eq, sub_self]
  unfold wellInteraction Sh
  apply ContinuousLinearMap.ext
  intro f
  change Qh h (resolvent D le_rfl (by positivity) (fieldTranslation (-latticeShift 0) (Qh h f))) = _
  have hz : latticeShift (0 : Bloch.Alias) = 0 := by
    apply PiLp.ext
    intro j
    simp only [latticeShift, PiLp.smul_apply, integerVector_apply, Pi.zero_apply,
      Int.cast_zero, smul_zero]
    rfl
  rw [hz, neg_zero, fieldTranslation_zero]
  rfl

#print axioms resolvent_lattice_translation
#print axioms site_interaction_eq

end Maxwell.Continuum.FiniteAuxiliary
