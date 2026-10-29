import Maxwell.Continuum.FourierTranslation
import Maxwell.Continuum.PeriodicMaterial
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Literal translation differences of the scalar periodic dielectric,
and their induced bounded commutator on physical L². -/

noncomputable section

namespace Maxwell.Continuum

open MeasureTheory

namespace Bloch

def translationOperator (a : Space) : FieldL2 →L[ℂ] FieldL2 :=
  (fieldTranslation a).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem translationOperator_apply (a : Space) (f : FieldL2) :
    translationOperator a f = fieldTranslation a f := rfl

theorem translationOperator_norm_le (a : Space) : ‖translationOperator a‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [translationOperator_apply, (fieldTranslation a).norm_map, one_mul] using le_refl ‖f‖

theorem translationOperator_neg_mul (a : Space) :
    translationOperator a * translationOperator (-a) = 1 := by
  apply ContinuousLinearMap.ext
  exact fieldTranslation_neg_apply a

end Bloch

namespace PeriodicMaterial

open Bloch FreeFiber

theorem cosine_translation_bound (a x : Space) (j : Fin 3) :
    |Real.cos (Real.pi * (x + a) j) - Real.cos (Real.pi * x j)| ≤ 4 * ‖a‖ := by
  have h := Real.abs_cos_sub_cos_le (Real.pi * (x + a) j) (Real.pi * x j)
  have ha : |a j| ≤ ‖a‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le a j
  have he : Real.pi * (x + a) j - Real.pi * x j = Real.pi * a j := by
    change Real.pi * (x j + a j) - Real.pi * x j = _
    ring
  rw [he, abs_mul, abs_of_pos Real.pi_pos] at h
  exact h.trans ((mul_le_mul_of_nonneg_left ha Real.pi_pos.le).trans
    (mul_le_mul_of_nonneg_right Real.pi_lt_four.le (norm_nonneg a)))

theorem periodicPotential_translation_bound (a x : Space) :
    |periodicPotential (x + a) - periodicPotential x| ≤ 28 * ‖a‖ := by
  have he : periodicPotential (x + a) - periodicPotential x =
      (Real.cos (Real.pi * (x + a) 0) - Real.cos (Real.pi * x 0)) +
      2 * (Real.cos (Real.pi * (x + a) 1) - Real.cos (Real.pi * x 1)) +
      4 * (Real.cos (Real.pi * (x + a) 2) - Real.cos (Real.pi * x 2)) := by
    unfold periodicPotential
    ring
  rw [he]
  let d : Fin 3 → ℝ := fun j => Real.cos (Real.pi * (x + a) j) - Real.cos (Real.pi * x j)
  have hb : |d 0 + 2 * d 1 + 4 * d 2| ≤ |d 0| + |2 * d 1| + |4 * d 2| :=
    (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  norm_num only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos (by norm_num : (0 : ℝ) < 4)] at hb
  dsimp only [d] at hb
  have h0 := cosine_translation_bound a x 0
  have h1 := cosine_translation_bound a x 1
  have h2 := cosine_translation_bound a x 2
  linarith

theorem coefficient_translation_bound (a x : Space) :
    |coefficient (x + a) - coefficient x| ≤ 28 * ‖a‖ := by
  have he : coefficient (x + a) - coefficient x =
      backgroundAmplitude * (periodicPotential (x + a) - periodicPotential x) := by
    unfold coefficient
    ring
  rw [he, abs_mul, abs_of_pos backgroundAmplitude_pos]
  have hρ : backgroundAmplitude ≤ 1 := backgroundAmplitude_le.trans (by norm_num)
  calc
    _ ≤ 1 * |periodicPotential (x + a) - periodicPotential x| :=
      mul_le_mul_of_nonneg_right hρ (abs_nonneg _)
    _ ≤ 28 * ‖a‖ := by simpa only [one_mul] using periodicPotential_translation_bound a x

def translationCommutator (a : Space) : FieldL2 →L[ℂ] FieldL2 :=
  translationOperator a * dielectric.multiplier - dielectric.multiplier * translationOperator a

theorem translationCommutator_ae (a : Space) (f : FieldL2) (j : Fin 3) :
    translationCommutator a f j =ᵐ[volume] (fun x =>
      ((coefficient (x + a) - coefficient x : ℝ) : ℂ) * f j (x + a)) := by
  have hp := (measurePreserving_add_right volume a).quasiMeasurePreserving.ae_eq_comp
    (dielectric.multiplier_ae f j)
  filter_upwards [fieldTranslation_ae a (dielectric.multiplier f) j,
    dielectric.multiplier_ae (fieldTranslation a f) j, fieldTranslation_ae a f j,
    Lp.coeFn_sub (fieldTranslation a (dielectric.multiplier f) j)
      (dielectric.multiplier (fieldTranslation a f) j), hp] with x ht hm hf hs hp
  change (fieldTranslation a (dielectric.multiplier f) j -
    dielectric.multiplier (fieldTranslation a f) j) x = _
  dsimp only [Function.comp_apply] at hp
  rw [hs]
  simp only [Pi.sub_apply]
  rw [ht, hp, hm, hf]
  change (coefficient (x + a) : ℂ) * f j (x + a) -
    (coefficient x : ℂ) * f j (x + a) = _
  rw [Complex.ofReal_sub, sub_mul]

theorem translationCommutator_component_norm (a : Space) (f : FieldL2) (j : Fin 3) :
    ‖translationCommutator a f j‖ ≤ (28 * ‖a‖) * ‖f j‖ := by
  rw [← (translation a).norm_map (f j)]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [translationCommutator_ae a f j, translation_ae a (f j)] with x hc ht
  rw [hc, ht, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (coefficient_translation_bound a x) (norm_nonneg _)

theorem translationCommutator_norm_le (a : Space) :
    ‖translationCommutator a‖ ≤ 28 * ‖a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  rw [← mul_pow]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
    (translationCommutator_component_norm a f j)

end PeriodicMaterial
end Maxwell.Continuum
