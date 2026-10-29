import Maxwell.Continuum.AuxiliaryTranslationGraph

/-! Quantitative translation stability of the literal whole-space cutoff
resolvent, with the paper's constants and physical length parameter. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Auxiliary

open Bloch

theorem resolventTranslationCommutator_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64) (a : Space) :
    ‖resolventTranslationCommutator D hσ0 hσ a‖ ≤ 448 * (h ^ 4)⁻¹ * ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  calc
    _ ≤ (4 * (h ^ 2)⁻¹) *
        ‖PeriodicMaterial.translationCommutator a (resolvent D hσ0 hσ f)‖ :=
      resolventTranslationCommutator_source_bound D hσ0 hσ a f
    _ ≤ (4 * (h ^ 2)⁻¹) * ((28 * ‖a‖) * ‖resolvent D hσ0 hσ f‖) :=
      mul_le_mul_of_nonneg_left
        ((PeriodicMaterial.translationCommutator a).le_of_opNorm_le
          (PeriodicMaterial.translationCommutator_norm_le a) _) (by positivity)
    _ ≤ (4 * (h ^ 2)⁻¹) * ((28 * ‖a‖) * ((4 * (h ^ 2)⁻¹) * ‖f‖)) := by
      gcongr
      exact (resolvent D hσ0 hσ).le_of_opNorm_le (resolvent_norm_le D hσ0 hσ) f
    _ = (448 * (h ^ 4)⁻¹ * ‖a‖) * ‖f‖ := by
      simp only [← inv_pow]
      ring

theorem resolvent_translation_difference {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64) (a : Space) :
    translationOperator a * resolvent D hσ0 hσ * translationOperator (-a) -
      resolvent D hσ0 hσ =
        resolventTranslationCommutator D hσ0 hσ a * translationOperator (-a) := by
  unfold resolventTranslationCommutator
  rw [sub_mul, mul_assoc (resolvent D hσ0 hσ), translationOperator_neg_mul, mul_one]

theorem resolvent_translation_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64) (a : Space) :
    ‖translationOperator a * resolvent D hσ0 hσ * translationOperator (-a) -
      resolvent D hσ0 hσ‖ ≤ (2 : ℝ)^20 * (h ^ 4)⁻¹ * ‖a‖ := by
  rw [resolvent_translation_difference]
  calc
    _ ≤ ‖resolventTranslationCommutator D hσ0 hσ a‖ * ‖translationOperator (-a)‖ :=
      norm_mul_le _ _
    _ ≤ (448 * (h ^ 4)⁻¹ * ‖a‖) * 1 :=
      mul_le_mul (resolventTranslationCommutator_norm_le D hσ0 hσ a)
        (translationOperator_norm_le (-a)) (norm_nonneg _) (by positivity)
    _ ≤ (2 : ℝ)^20 * (h ^ 4)⁻¹ * ‖a‖ := by
      rw [mul_one]
      gcongr
      norm_num

/-- The displayed L⁴ bound is for the actual translated operator, with
no assumption that translated and untranslated maximal domains agree. -/
theorem resolvent_translation_norm_le_length {L z σ : ℝ} (D : Calibration L⁻¹ z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹) ^ 4 / 64) (a : Space) :
    ‖translationOperator a * resolvent D hσ0 hσ * translationOperator (-a) -
      resolvent D hσ0 hσ‖ ≤ (2 : ℝ)^20 * L ^ 4 * ‖a‖ := by
  simpa only [inv_pow, inv_inv] using resolvent_translation_norm_le D hσ0 hσ a

#print axioms resolvent_translation_norm_le_length
#print axioms cutoffOperator_translation
#print axioms cutoffFiber_translation_identity

end Maxwell.Continuum.Auxiliary
