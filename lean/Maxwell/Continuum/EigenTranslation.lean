import Maxwell.Continuum.TranslationContinuity

/-! A real normalized isolated eigenvector inherits a local translation
bound from the actual operator commutator and a precise complement gap. -/

noncomputable section

namespace Maxwell.Continuum.EigenTranslation

open Bloch Filter
open scoped Topology

theorem normalized_real_distance {u w : FieldL2} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1)
    (hi : (inner ℂ u w).im = 0) (hp : 0 ≤ (inner ℂ u w).re) :
    ‖w - u‖ ≤ 2 * ‖w - inner ℂ u w • u‖ := by
  let c : ℝ := (inner ℂ u w).re
  have hc : 0 ≤ c := hp
  have hC : (c : ℂ) = inner ℂ u w := by
    apply Complex.ext
    · rfl
    · simpa using hi.symm
  have hc1 : c ≤ 1 := by
    exact (Complex.re_le_norm _).trans
      (by simpa only [hu, hw, one_mul] using (norm_inner_le_norm (𝕜 := ℂ) u w))
  have hwu : (inner ℂ w u).re = c := by
    exact inner_re_symm (𝕜 := ℂ) w u
  have hd : ‖w - u‖ ^ 2 = 2 - 2 * c := by
    rw [norm_sub_sq (𝕜 := ℂ), hw, hu]
    change 1 ^ 2 - 2 * (inner ℂ w u).re + 1 ^ 2 = _
    rw [hwu]
    ring
  have hv : ‖w - (c : ℂ) • u‖ ^ 2 = 1 - c ^ 2 := by
    rw [norm_sub_sq (𝕜 := ℂ), hw, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hc, hu, inner_smul_right]
    change 1 ^ 2 - 2 * ((c : ℂ) * inner ℂ w u).re + (c * 1) ^ 2 = _
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [hwu]
    ring
  rw [← hC]
  nlinarith [mul_nonneg hc (sub_nonneg.mpr hc1), norm_nonneg (w - u),
    norm_nonneg (w - (c : ℂ) • u)]

/-- The gap is the actual residual bound on u⊥. No regularity or
translation modulus is included among the mode assumptions. -/
structure IsolatedRealMode (S : FieldL2 →L[ℂ] FieldL2) (μ g : ℝ) (u : FieldL2) : Prop where
  unit_norm : ‖u‖ = 1
  real : fieldConjugation u = u
  eigenvector : S u = (μ : ℂ) • u
  gap_pos : 0 < g
  gap : ∀ v : FieldL2, inner ℂ u v = 0 → g * ‖v‖ ≤ ‖S v - (μ : ℂ) • v‖

namespace IsolatedRealMode

variable {S : FieldL2 →L[ℂ] FieldL2} {μ g : ℝ} {u : FieldL2}
variable (D : IsolatedRealMode S μ g u)
include D

theorem translated_inner_real (a : Space) : (inner ℂ u (fieldTranslation a u)).im = 0 :=
  inner_im_zero_of_real D.real (fieldTranslation_preserves_real a D.real)

theorem translated_inner_positive :
    ∀ᶠ a : Space in 𝓝 0, 0 ≤ (inner ℂ u (fieldTranslation a u)).re := by
  have hc : Continuous (fun a : Space => (inner ℂ u (fieldTranslation a u)).re) :=
    Complex.continuous_re.comp (continuous_const.inner (fieldTranslation_continuous u))
  have h0 : 0 < (inner ℂ u (fieldTranslation 0 u)).re := by
    rw [fieldTranslation_zero, inner_self_eq_norm_sq_to_K, D.unit_norm]
    norm_num
  exact (hc.continuousAt.eventually (eventually_gt_nhds h0)).mono (fun _ h => h.le)

theorem transverse_bound (a : Space) {C : ℝ}
    (hC : ‖translationOperator a * S - S * translationOperator a‖ ≤ C * ‖a‖) :
    g * ‖fieldTranslation a u - inner ℂ u (fieldTranslation a u) • u‖ ≤ C * ‖a‖ := by
  let w := fieldTranslation a u
  let c := inner ℂ u w
  let v := w - c • u
  have huv : inner ℂ u v = 0 := by
    change inner ℂ u (w - c • u) = 0
    rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, D.unit_norm]
    simp [c]
  have hg := D.gap v huv
  have he : S v - (μ : ℂ) • v =
      -((translationOperator a * S - S * translationOperator a) u) := by
    change S (w - c • u) - (μ : ℂ) • (w - c • u) =
      -(fieldTranslation a (S u) - S w)
    rw [map_sub, map_smul, D.eigenvector, map_smul, smul_sub, smul_smul, smul_smul]
    rw [mul_comm c (μ : ℂ)]
    change S w - ((μ : ℂ) * c) • u - ((μ : ℂ) • w - ((μ : ℂ) * c) • u) =
      -((μ : ℂ) • w - S w)
    abel
  rw [he, norm_neg] at hg
  exact hg.trans (by simpa only [D.unit_norm, mul_one] using
    (translationOperator a * S - S * translationOperator a).le_of_opNorm_le hC u)

theorem translation_bound {C : ℝ}
    (hC : ∀ a : Space, ‖translationOperator a * S - S * translationOperator a‖ ≤ C * ‖a‖) :
    ∀ᶠ a : Space in 𝓝 0, ‖fieldTranslation a u - u‖ ≤ (2 * C / g) * ‖a‖ := by
  filter_upwards [D.translated_inner_positive] with a ha
  have hd := normalized_real_distance D.unit_norm ((fieldTranslation a).norm_map u |>.trans D.unit_norm)
    (D.translated_inner_real a) ha
  have ht := D.transverse_bound a (hC a)
  have hdiv : ‖fieldTranslation a u - inner ℂ u (fieldTranslation a u) • u‖ ≤ C * ‖a‖ / g :=
    (le_div_iff₀ D.gap_pos).mpr (by simpa only [mul_comm] using ht)
  calc
    _ ≤ 2 * (C * ‖a‖ / g) := hd.trans (mul_le_mul_of_nonneg_left hdiv (by norm_num))
    _ = (2 * C / g) * ‖a‖ := by ring

end IsolatedRealMode

end Maxwell.Continuum.EigenTranslation
