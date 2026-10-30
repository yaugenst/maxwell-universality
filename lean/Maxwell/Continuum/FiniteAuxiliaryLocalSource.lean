import Maxwell.Continuum.FiniteAuxiliaryWellTranslation
import Maxwell.Continuum.EffectiveMassRealMode

/-! The literal local source Q_h u_h has actual H¹ regularity, obtained
without applying the unbounded Maxwell operator to its definition. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 2048

namespace Maxwell.Continuum.FiniteAuxiliary

open Auxiliary EffectiveMass Bloch FourierSobolev Filter MeasureTheory
open scoped Topology

attribute [local irreducible] realMode Sh muH Qh

def localSource {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024) : FieldL2 :=
  Qh h (realMode D hh)

theorem localSource_norm_le {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024) :
    ‖localSource D hh‖ ≤ 1 := by
  have he := (Qh h).le_of_opNorm_le (Qh_norm_le h) (realMode D hh)
  simpa only [localSource, realMode_norm, mul_one] using he

theorem localSource_supported {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) :
    ∀ᵐ x ∂volume, h⁻¹ ≤ ‖x‖ → localSource D hh j x = 0 :=
  Qh_supported D.h_pos (realMode D hh) j

theorem localSource_translation_bound {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) :
    ∀ᶠ a : Space in 𝓝 0, ‖fieldTranslation a (localSource D hh)-localSource D hh‖ ≤
      (400*h+(2 : ℝ)^256*(h^2)⁻¹)*‖a‖ := by
  filter_upwards [Sh_mode_translation_bound D (realMode_isolated D hh)] with a ha
  have he : fieldTranslation a (localSource D hh)-localSource D hh =
      QhTranslationCommutator h a (realMode D hh)+
        Qh h (fieldTranslation a (realMode D hh)-realMode D hh) := by
    change fieldTranslation a (Qh h (realMode D hh))-Qh h (realMode D hh) =
      (fieldTranslation a (Qh h (realMode D hh))-Qh h (fieldTranslation a (realMode D hh)))+_
    rw [map_sub]
    abel
  have hc := (QhTranslationCommutator h a).le_of_opNorm_le
    (QhTranslationCommutator_norm_le h a) (realMode D hh)
  rw [realMode_norm, mul_one, abs_of_pos D.h_pos] at hc
  have hq := (Qh h).le_of_opNorm_le (Qh_norm_le h)
    (fieldTranslation a (realMode D hh)-realMode D hh)
  rw [one_mul] at hq
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add hc (hq.trans ha)).trans_eq (by ring))

def localSourceH1 {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024) :
    H1Data (localSource D hh) := h1OfTranslation _ (localSource_translation_bound D hh)

theorem localSourceH1_norm {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1/(2 : ℝ)^1024) :
    (localSourceH1 D hh).norm ≤ (2 : ℝ)^520*(h^2)⁻¹ := by
  have hp := D.h_pos
  have hb := h1OfTranslation_norm_le (localSource D hh)
    (show 0 ≤ 400*h+(2 : ℝ)^256*(h^2)⁻¹ by positivity) (localSource_translation_bound D hh)
  change (localSourceH1 D hh).norm ≤ _ at hb
  have hh1 : h ≤ 1 := hh.trans (by norm_num)
  have hinv : 1 ≤ (h^2)⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ (pow_pos hp 2)).mpr
    nlinarith only [hp, hh1]
  have hc : (1201 : ℝ)+3*2^256 ≤ 2^520 := by norm_num
  have hc' := mul_le_mul_of_nonneg_right hc (inv_nonneg.mpr (sq_nonneg h))
  have hhn := localSource_norm_le D hh
  have hhi : h ≤ (h^2)⁻¹ := hh1.trans hinv
  nlinarith only [hb, hinv, hhi, hc', hhn]

#print axioms localSourceH1_norm

end Maxwell.Continuum.FiniteAuxiliary
