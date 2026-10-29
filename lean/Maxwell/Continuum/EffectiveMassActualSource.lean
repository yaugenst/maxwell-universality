import Maxwell.Continuum.EffectiveMassSourceMode
import Maxwell.Continuum.EffectiveMassRealMode

/-! The source identities for the literal constructed auxiliary mode,
with its eigenvector and eigenvalue hypotheses discharged. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 1024

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory Auxiliary Bloch FourierSobolev Filter
open scoped Topology

attribute [local irreducible] realMode muH Auxiliary.resolvent Sh Qh Wh

def actualSource {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1 / (2 : ℝ)^1024) : FieldL2 :=
  sourceMode h (realMode D hh)

theorem actualSource_ne_zero {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1 / (2 : ℝ)^1024) :
    actualSource D hh ≠ 0 := by
  apply sourceMode_ne_zero D (muH_pos D hh).ne' (realMode_eigen D hh)
  intro he
  have hn := realMode_norm D hh
  rw [he, norm_zero] at hn
  exact zero_ne_one hn

theorem actualSource_norm_le {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1 / (2 : ℝ)^1024) :
    ‖actualSource D hh‖ ≤ 1 := by
  exact (sourceMode_norm_le h (realMode D hh)).trans_eq (realMode_norm D hh)

theorem actualSource_supported {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    ∀ᵐ x ∂(volume : Measure Space), h⁻¹ ≤ ‖x‖ → actualSource D hh j x = 0 :=
  sourceMode_supported D.h_pos (realMode D hh) j

theorem actualSource_real {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) : fieldConjugation (actualSource D hh) = actualSource D hh :=
  sourceMode_real h (realMode_real D hh)

theorem actualSource_equation {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) :
    actualSource D hh = (muH D hh : ℂ)⁻¹ •
      Wh h (resolvent D le_rfl (by positivity) (actualSource D hh)) :=
  sourceMode_equation D (muH_pos D hh).ne' (realMode_eigen D hh)

theorem actualSource_translation_bound {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) :
    ∀ᶠ a : Space in 𝓝 0,
      ‖fieldTranslation a (actualSource D hh) - actualSource D hh‖ ≤
        ((2 : ℝ)^257 * (h^2)⁻¹) * ‖a‖ := by
  have hb := Sh_mode_translation_bound D (realMode_isolated D hh)
  have h1 : h ≤ 1 := (calibration_h_small D).trans (by norm_num)
  have h2 : h^2 ≤ 1 := by nlinarith [D.h_pos]
  have hi : 1 ≤ (h^2)⁻¹ := (one_le_inv₀ (sq_pos_of_pos D.h_pos)).mpr h2
  filter_upwards [hb] with a ha
  have he : fieldTranslation a (actualSource D hh) - actualSource D hh =
      QhTranslationCommutator h a (realMode D hh) +
        Qh h (fieldTranslation a (realMode D hh) - realMode D hh) := by
    change fieldTranslation a (Qh h (realMode D hh)) - Qh h (realMode D hh) = _
    change fieldTranslation a (Qh h (realMode D hh)) - Qh h (realMode D hh) =
      (fieldTranslation a (Qh h (realMode D hh)) - Qh h (fieldTranslation a (realMode D hh))) + _
    rw [map_sub]
    abel
  rw [he]
  have hc := (QhTranslationCommutator h a).le_of_opNorm_le
    (QhTranslationCommutator_norm_le h a) (realMode D hh)
  rw [realMode_norm, mul_one, abs_of_pos D.h_pos] at hc
  have hq := (Qh h).le_of_opNorm_le (Qh_norm_le h)
    (fieldTranslation a (realMode D hh) - realMode D hh)
  rw [one_mul] at hq
  have hconst : 400 * h + (2 : ℝ)^256 * (h^2)⁻¹ ≤ (2 : ℝ)^257 * (h^2)⁻¹ := by
    have hp : (400 : ℝ) ≤ (2 : ℝ)^256 := by norm_num
    have he2 : (2 : ℝ)^257 = 2 * (2 : ℝ)^256 := by rw [pow_succ]; ring
    rw [he2]
    nlinarith
  calc
    _ ≤ (400 * h * ‖a‖) + ((2 : ℝ)^256 * (h^2)⁻¹) * ‖a‖ :=
      (norm_add_le _ _).trans (add_le_add hc (hq.trans ha))
    _ = (400 * h + (2 : ℝ)^256 * (h^2)⁻¹) * ‖a‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hconst (norm_nonneg a)

def actualSourceH1 {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) : H1Data (actualSource D hh) :=
  h1OfTranslation (actualSource D hh) (actualSource_translation_bound D hh)

theorem actualSourceH1_norm_le {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) :
    (actualSourceH1 D hh).norm ≤ (2 : ℝ)^512 * (h^2)⁻¹ := by
  have hb := h1OfTranslation_norm_le (actualSource D hh)
    (show 0 ≤ (2 : ℝ)^257 * (h^2)⁻¹ by positivity) (actualSource_translation_bound D hh)
  have h2 : h^2 ≤ 1 := by nlinarith [calibration_h_small D, D.h_pos]
  have hi : 1 ≤ (h^2)⁻¹ := (one_le_inv₀ (sq_pos_of_pos D.h_pos)).mpr h2
  have hc : 1 + 3 * (2 : ℝ)^257 ≤ (2 : ℝ)^512 := by norm_num
  change (actualSourceH1 D hh).norm ≤ _ at hb
  calc
    _ ≤ 1 + 3 * ((2 : ℝ)^257 * (h^2)⁻¹) :=
      hb.trans (add_le_add (actualSource_norm_le D hh) le_rfl)
    _ ≤ (1 + 3 * (2 : ℝ)^257) * (h^2)⁻¹ := by nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)

#print axioms actualSource_ne_zero
#print axioms actualSource_equation
#print axioms actualSource_real
#print axioms actualSourceH1_norm_le

end Maxwell.Continuum.EffectiveMass
