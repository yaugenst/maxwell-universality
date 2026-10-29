import Maxwell.Continuum.TranslationH1
import Maxwell.Continuum.EigenTranslation

/-! The paper's H¹ estimate follows from the actual Sh commutator and
its explicit isolated-mode gap. The spectral gap remains visible as the
input discharged by the independent effective-mass eigenpair theorem. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.EffectiveMass

open Auxiliary Bloch FourierSobolev EigenTranslation Filter
open scoped Topology

def modeGap (h : ℝ) : ℝ := ((2 : ℝ)^192)⁻¹ * (h^2)⁻¹

theorem modeGap_pos {h : ℝ} (hh : 0 < h) : 0 < modeGap h := by
  dsimp [modeGap]
  positivity

theorem Sh_mode_translation_bound {h z μ : ℝ} {u : FieldL2}
    (D : Calibration h z) (hu : IsolatedRealMode (Sh D) μ (modeGap h) u) :
    ∀ᶠ a : Space in 𝓝 0,
      ‖fieldTranslation a u - u‖ ≤ ((2 : ℝ)^256 * (h^2)⁻¹) * ‖a‖ := by
  have hb := hu.translation_bound (fun a => Sh_translationCommutator_norm_le D a)
  have he : 2 * ((2 : ℝ)^32 * (h^4)⁻¹) / modeGap h = (2 : ℝ)^225 * (h^2)⁻¹ := by
    dsimp [modeGap]
    field_simp [ne_of_gt D.h_pos]
  have hc : (2 : ℝ)^225 * (h^2)⁻¹ ≤ (2 : ℝ)^256 * (h^2)⁻¹ :=
    mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  filter_upwards [hb] with a ha
  rw [he] at ha
  exact ha.trans (mul_le_mul_of_nonneg_right hc (norm_nonneg a))

def Sh_modeH1 {h z μ : ℝ} {u : FieldL2}
    (D : Calibration h z) (hu : IsolatedRealMode (Sh D) μ (modeGap h) u) : H1Data u :=
  h1OfTranslation u (Sh_mode_translation_bound D hu)

theorem Sh_modeH1_norm_le {h z μ : ℝ} {u : FieldL2}
    (D : Calibration h z) (hu : IsolatedRealMode (Sh D) μ (modeGap h) u) :
    (Sh_modeH1 D hu).norm ≤ (2 : ℝ)^512 * (h^2)⁻¹ := by
  have hb := h1OfTranslation_norm_le u
    (show 0 ≤ (2 : ℝ)^256 * (h^2)⁻¹ by positivity) (Sh_mode_translation_bound D hu)
  change (Sh_modeH1 D hu).norm ≤ _ at hb
  rw [hu.unit_norm] at hb
  have hh1 : h ≤ 1 := (calibration_h_small D).trans (by norm_num)
  have hh2 : h^2 ≤ 1 := by nlinarith [D.h_pos]
  have hx : 1 ≤ (h^2)⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (pow_pos D.h_pos 2)).mpr
    simpa only [one_mul] using hh2
  have hc : 1 + 3 * (2 : ℝ)^256 ≤ (2 : ℝ)^512 := by
    have hp : 1 ≤ (2 : ℝ)^256 := one_le_pow₀ (by norm_num)
    calc
      _ ≤ 4 * (2 : ℝ)^256 := by linarith
      _ = (2 : ℝ)^258 := by
        rw [show (258 : ℕ) = 2 + 256 by omega, pow_add]
        norm_num
      _ ≤ (2 : ℝ)^512 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  calc
    _ ≤ 1 + 3 * ((2 : ℝ)^256 * (h^2)⁻¹) := hb
    _ ≤ (1 + 3 * (2 : ℝ)^256) * (h^2)⁻¹ := by nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)

theorem Sh_modeH1_norm_le_length {L z μ : ℝ} {u : FieldL2}
    (D : Calibration L⁻¹ z) (hu : IsolatedRealMode (Sh D) μ (modeGap L⁻¹) u) :
    (Sh_modeH1 D hu).norm ≤ (2 : ℝ)^512 * L^2 := by
  simpa only [inv_pow, inv_inv] using Sh_modeH1_norm_le D hu

#print axioms Sh_modeH1_norm_le_length
#print axioms FourierSobolev.derivative_eLpNorm_le
#print axioms FourierSobolev.weakDerivative_distribution

end Maxwell.Continuum.EffectiveMass
