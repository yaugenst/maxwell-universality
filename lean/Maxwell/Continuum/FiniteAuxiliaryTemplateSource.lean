import Maxwell.Continuum.FiniteAuxiliaryTemplateReadout
import Maxwell.Continuum.FiniteAuxiliaryIdealSource

/-! Literal finite-template source synthesis and error control for the
shared scalar, template approximation and dyadic amplitude rounding. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

open MeasureTheory EffectiveMass Auxiliary

variable {ι : Type*} [Fintype ι]

theorem templateSynthesis_sub (a b : ι → FieldL2) :
    templateSynthesis a-templateSynthesis b = templateSynthesis (fun i => a i-b i) := by
  apply ContinuousLinearMap.ext
  intro g
  simp only [sub_apply, templateSynthesis_apply, smul_sub, Finset.sum_sub_distrib]

theorem templateSynthesis_error {δ : ℝ} (hδ : 0 ≤ δ)
    (a b : ι → FieldL2) (hab : ∀ i, ‖a i-b i‖ ≤ δ)
    (s : ι → Set Space) (hs : Pairwise fun i j => Disjoint (s i) (s j))
    (hsab : ∀ i k, ∀ᵐ x ∂volume, x ∉ s i → (a i-b i) k x = 0) :
    ‖templateSynthesis a-templateSynthesis b‖ ≤ δ := by
  rw [templateSynthesis_sub]
  exact templateSynthesis_norm hδ _ hab (fun i j hij =>
    field_inner_eq_zero_of_disjoint (hs hij) (hsab i) (hsab j))

theorem templateSource_error (a b : ι → FieldL2) {M δ : ℝ}
    (hM : ‖templateSynthesis a‖ ≤ M) (hδ : ‖templateSynthesis a-templateSynthesis b‖ ≤ δ)
    (c ĉ : ℝ) (g y : BrightSpace ι) :
    ‖templateSynthesis a y-(c : ℂ) • templateSynthesis b g‖ ≤
      M*(‖y-(ĉ : ℂ) • g‖+|ĉ-c| * ‖g‖)+|c| * δ*‖g‖ := by
  have hM0 := (norm_nonneg _).trans hM
  have he : templateSynthesis a y-(c : ℂ) • templateSynthesis b g =
      templateSynthesis a (y-(c : ℂ) • g)+
        (c : ℂ) • (templateSynthesis a-templateSynthesis b) g := by
    simp only [map_sub, map_smul, sub_apply, smul_sub]
    abel
  have hy : ‖y-(c : ℂ) • g‖ ≤ ‖y-(ĉ : ℂ) • g‖+|ĉ-c| * ‖g‖ := by
    have hei : y-(c : ℂ) • g = (y-(ĉ : ℂ) • g)+((ĉ-c : ℝ) : ℂ) • g := by
      rw [Complex.ofReal_sub, sub_smul]
      abel
    rw [hei]
    simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs] using norm_add_le (y-(ĉ : ℂ) • g)
      (((ĉ-c : ℝ) : ℂ) • g)
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact ((templateSynthesis a).le_of_opNorm_le hM _).trans
      (mul_le_mul_of_nonneg_left hy hM0)
  · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      ((templateSynthesis a-templateSynthesis b).le_of_opNorm_le hδ g) (abs_nonneg c)

theorem templateSource_error_budget (a b : ι → FieldL2) {e c ĉ : ℝ}
    (he : 0 ≤ e) (hA : ‖templateSynthesis a‖ ≤ 2)
    (hab : ‖templateSynthesis a-templateSynthesis b‖ ≤ e/4)
    (hc : |c| ≤ 1) (hĉ : |ĉ-c| ≤ e/16) (g y : BrightSpace ι)
    (hy : ‖y-(ĉ : ℂ) • g‖ ≤ e*‖g‖/16) :
    ‖templateSynthesis a y-(c : ℂ) • templateSynthesis b g‖ ≤ e*‖g‖ := by
  have hn := templateSource_error a b hA hab c ĉ g y
  have hc' := mul_le_mul_of_nonneg_right hc (show 0 ≤ (e/4)*‖g‖ by positivity)
  have hĉ' := mul_le_mul_of_nonneg_right hĉ (norm_nonneg g)
  have hge := mul_nonneg he (norm_nonneg g)
  nlinarith only [hn, hc', hĉ', hy, hge]

theorem idealSource_templateSynthesis {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (r : ι → Space) (α : ℝ) (g : BrightSpace ι) :
    idealSource D hh r α g = ((α/muH D hh : ℝ) : ℂ) •
      templateSynthesis (fun i => siteInsertion h (r i) (realMode D hh)) g := by
  rw [idealSource_eq, insertion_apply, templateSynthesis_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [bright_apply, map_smul]

#print axioms templateSource_error_budget
#print axioms idealSource_templateSynthesis

end Maxwell.Continuum.FiniteAuxiliary
