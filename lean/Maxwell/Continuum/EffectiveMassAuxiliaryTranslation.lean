import Maxwell.Continuum.WellTranslation
import Maxwell.Continuum.AuxiliaryTranslationBounds

/-! The literal physical auxiliary operator Sh = Qh R0 Qh and its
translation stability. All factors are the constructed continuum maps. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.EffectiveMass

open Auxiliary Bloch

def Sh {h z : ℝ} (D : Calibration h z) : FieldL2 →L[ℂ] FieldL2 :=
  Qh h * resolvent D le_rfl (by positivity) * Qh h

theorem Sh_norm_le {h z : ℝ} (D : Calibration h z) : ‖Sh D‖ ≤ 4 * (h ^ 2)⁻¹ := by
  calc
    _ ≤ (‖Qh h‖ * ‖resolvent D le_rfl (by positivity)‖) * ‖Qh h‖ :=
      (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * (4 * (h ^ 2)⁻¹)) * 1 := by
      gcongr
      · exact Qh_norm_le h
      · exact resolvent_norm_le D le_rfl (by positivity)
      · exact Qh_norm_le h
    _ = _ := by ring

theorem Sh_selfAdjoint {h z : ℝ} (D : Calibration h z) : IsSelfAdjoint (Sh D) := by
  change star (Qh h * resolvent D le_rfl (by positivity) * Qh h) = _
  simp only [star_mul, (Qh_selfAdjoint h).star_eq,
    (resolvent_selfAdjoint D le_rfl (by positivity)).star_eq, mul_assoc]
  rfl

theorem sandwich_commutator_bound (T Q R : FieldL2 →L[ℂ] FieldL2)
    {r c d : ℝ} (hr : 0 ≤ r) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hQ : ‖Q‖ ≤ 1) (hR : ‖R‖ ≤ r)
    (hC : ‖T * Q - Q * T‖ ≤ c) (hD : ‖T * R - R * T‖ ≤ d) :
    ‖T * (Q * R * Q) - (Q * R * Q) * T‖ ≤ 2 * c * r + d := by
  have he : T * (Q * R * Q) - (Q * R * Q) * T =
      (T * Q - Q * T) * R * Q + Q * (T * R - R * T) * Q + Q * R * (T * Q - Q * T) := by
    simp only [sub_mul, mul_sub, mul_assoc]
    abel
  rw [he]
  have h₁ : ‖(T * Q - Q * T) * R * Q‖ ≤ c * r := by
    calc
      _ ≤ (‖T * Q - Q * T‖ * ‖R‖) * ‖Q‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (c * r) * 1 := by gcongr
      _ = _ := mul_one _
  have h₂ : ‖Q * (T * R - R * T) * Q‖ ≤ d := by
    calc
      _ ≤ (‖Q‖ * ‖T * R - R * T‖) * ‖Q‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (1 * d) * 1 := by gcongr
      _ = _ := by ring
  have h₃ : ‖Q * R * (T * Q - Q * T)‖ ≤ r * c := by
    calc
      _ ≤ (‖Q‖ * ‖R‖) * ‖T * Q - Q * T‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ ≤ (1 * r) * c := by gcongr
      _ = _ := by ring
  calc
    _ ≤ ‖(T * Q - Q * T) * R * Q‖ + ‖Q * (T * R - R * T) * Q‖ +
        ‖Q * R * (T * Q - Q * T)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 2 * c * r + d := by nlinarith

theorem inverse_square_le_inverse_fourth {h z : ℝ} (D : Calibration h z) :
    (h ^ 2)⁻¹ ≤ (h ^ 4)⁻¹ := by
  have h1 : h ≤ 1 := (calibration_h_small D).trans (by norm_num)
  have h2 : h ^ 2 ≤ 1 := by nlinarith [D.h_pos]
  have h4 : h ^ 4 ≤ h ^ 2 := by nlinarith [sq_nonneg (h ^ 2), sq_nonneg h]
  exact (inv_le_inv₀ (pow_pos D.h_pos 2) (pow_pos D.h_pos 4)).mpr h4

theorem Sh_translationCommutator_norm_le {h z : ℝ} (D : Calibration h z) (a : Space) :
    ‖translationOperator a * Sh D - Sh D * translationOperator a‖ ≤
      (2 : ℝ)^32 * (h ^ 4)⁻¹ * ‖a‖ := by
  have hb := sandwich_commutator_bound (translationOperator a) (Qh h)
    (resolvent D le_rfl (by positivity))
    (r := 4 * (h ^ 2)⁻¹) (c := 400 * |h| * ‖a‖) (d := 448 * (h ^ 4)⁻¹ * ‖a‖)
    (by positivity) (by positivity) (by positivity) (Qh_norm_le h)
    (resolvent_norm_le D le_rfl (by positivity))
    (QhTranslationCommutator_norm_le h a)
    (resolventTranslationCommutator_norm_le D le_rfl (by positivity) a)
  change ‖translationOperator a * Sh D - Sh D * translationOperator a‖ ≤ _ at hb
  have h1 : |h| ≤ 1 := by rw [abs_of_pos D.h_pos]; linarith [calibration_h_small D]
  have hterm : 2 * (400 * |h| * ‖a‖) * (4 * (h ^ 2)⁻¹) ≤
      3200 * (h ^ 4)⁻¹ * ‖a‖ := by
    calc
      _ ≤ 2 * (400 * 1 * ‖a‖) * (4 * (h ^ 2)⁻¹) := by gcongr
      _ ≤ 2 * (400 * 1 * ‖a‖) * (4 * (h ^ 4)⁻¹) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (inverse_square_le_inverse_fourth D) (by norm_num))
          (by positivity)
      _ = _ := by ring
  have hp : 0 ≤ (h ^ 4)⁻¹ * ‖a‖ := by positivity
  nlinarith

theorem Sh_translation_norm_le {h z : ℝ} (D : Calibration h z) (a : Space) :
    ‖translationOperator a * Sh D * translationOperator (-a) - Sh D‖ ≤
      (2 : ℝ)^32 * (h ^ 4)⁻¹ * ‖a‖ := by
  have he : translationOperator a * Sh D * translationOperator (-a) - Sh D =
      (translationOperator a * Sh D - Sh D * translationOperator a) * translationOperator (-a) := by
    rw [sub_mul, mul_assoc (Sh D), translationOperator_neg_mul, mul_one]
  rw [he]
  calc
    _ ≤ ‖translationOperator a * Sh D - Sh D * translationOperator a‖ * ‖translationOperator (-a)‖ :=
      norm_mul_le _ _
    _ ≤ ((2 : ℝ)^32 * (h ^ 4)⁻¹ * ‖a‖) * 1 :=
      mul_le_mul (Sh_translationCommutator_norm_le D a) (translationOperator_norm_le (-a))
        (norm_nonneg _) (by positivity)
    _ = _ := mul_one _

theorem Sh_translation_norm_le_length {L z : ℝ} (D : Calibration L⁻¹ z) (a : Space) :
    ‖translationOperator a * Sh D * translationOperator (-a) - Sh D‖ ≤
      (2 : ℝ)^32 * L ^ 4 * ‖a‖ := by
  simpa only [inv_pow, inv_inv] using Sh_translation_norm_le D a

#print axioms Sh_translation_norm_le_length
#print axioms Sh_selfAdjoint

end Maxwell.Continuum.EffectiveMass
