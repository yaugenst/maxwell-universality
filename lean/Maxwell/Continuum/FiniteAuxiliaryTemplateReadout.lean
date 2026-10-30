import Maxwell.Continuum.FiniteAuxiliaryOrthogonal
import Maxwell.Continuum.FiniteAuxiliaryReadout

/-! Finite moment maps for actual physical templates. Disjoint supports
control template perturbations without a factor depending on the number
of wells. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.FiniteAuxiliary

open MeasureTheory

variable {ι : Type*} [Fintype ι]

def templateSynthesis (a : ι → FieldL2) : BrightSpace ι →L[ℂ] FieldL2 :=
  ∑ i, (ContinuousLinearMap.toSpanSingleton ℂ (a i)).comp
    (PiLp.proj 2 (fun _ : ι => ℂ) i)

theorem templateSynthesis_apply (a : ι → FieldL2) (g : BrightSpace ι) :
    templateSynthesis a g = ∑ i, g i • a i := by
  simp only [templateSynthesis, sum_apply, ContinuousLinearMap.comp_apply,
    PiLp.proj_apply, ContinuousLinearMap.toSpanSingleton_apply]

theorem templateSynthesis_norm {δ : ℝ} (hδ : 0 ≤ δ) (a : ι → FieldL2)
    (ha : ∀ i, ‖a i‖ ≤ δ)
    (ho : Pairwise fun i j => inner ℂ (a i) (a j) = 0) :
    ‖templateSynthesis a‖ ≤ δ := by
  apply ContinuousLinearMap.opNorm_le_bound _ hδ
  intro g
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hδ (norm_nonneg g))).mp
  rw [templateSynthesis_apply, orthogonal_sum_norm_sq _ (by
    intro i j hij
    rw [inner_smul_left, inner_smul_right, ho hij, mul_zero, mul_zero]),
    mul_pow, PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [norm_smul, mul_pow, mul_comm (δ^2)]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (ha i) 2) (sq_nonneg _)

def templateReadout (a : ι → FieldL2) : FieldL2 →L[ℂ] BrightSpace ι :=
  (templateSynthesis a).adjoint

theorem templateReadout_apply (a : ι → FieldL2) (f : FieldL2) (i : ι) :
    templateReadout a f i = inner ℂ (a i) f := by
  classical
  have he := (templateSynthesis a).adjoint_inner_right (PiLp.single 2 i 1) f
  simpa [templateReadout, templateSynthesis_apply, EuclideanSpace.inner_single_left,
    PiLp.single_apply] using he

theorem templateReadout_sub (a b : ι → FieldL2) :
    templateReadout a-templateReadout b = templateReadout (fun i => a i-b i) := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro i
  simp only [sub_apply, PiLp.sub_apply,
    templateReadout_apply, inner_sub_left]

theorem templateReadout_norm_of_disjoint {δ : ℝ} (hδ : 0 ≤ δ)
    (s : ι → Set Space) (hs : Pairwise fun i j => Disjoint (s i) (s j))
    (a : ι → FieldL2) (ha : ∀ i, ‖a i‖ ≤ δ)
    (hsa : ∀ i k, ∀ᵐ x ∂volume, x ∉ s i → a i k x = 0) :
    ‖templateReadout a‖ ≤ δ := by
  rw [templateReadout, LinearIsometryEquiv.norm_map]
  exact templateSynthesis_norm hδ a ha (fun i j hij =>
    field_inner_eq_zero_of_disjoint (hs hij) (hsa i) (hsa j))

def weightedTemplateReadout (v : ι → ℝ) (a : ι → FieldL2) :
    FieldL2 →L[ℂ] BrightSpace ι :=
  templateReadout (fun i => (v i : ℂ) • a i)

theorem weightedTemplateReadout_apply (v : ι → ℝ) (a : ι → FieldL2)
    (f : FieldL2) (i : ι) :
    weightedTemplateReadout v a f i = (v i : ℂ)*inner ℂ (a i) f := by
  rw [weightedTemplateReadout, templateReadout_apply, inner_smul_left]
  simp only [Complex.conj_ofReal]

theorem weightedTemplateReadout_error {V δ : ℝ} (hV : 0 ≤ V) (hδ : 0 ≤ δ)
    (v : ι → ℝ) (hv : ∀ i, |v i| ≤ V)
    (a b : ι → FieldL2) (hab : ∀ i, ‖a i-b i‖ ≤ δ)
    (s : ι → Set Space) (hs : Pairwise fun i j => Disjoint (s i) (s j))
    (hsab : ∀ i k, ∀ᵐ x ∂volume, x ∉ s i → (a i-b i) k x = 0) :
    ‖weightedTemplateReadout v a-weightedTemplateReadout v b‖ ≤ V*δ := by
  have he : weightedTemplateReadout v a-weightedTemplateReadout v b =
      templateReadout (fun i => (v i : ℂ) • (a i-b i)) := by
    simp only [weightedTemplateReadout, templateReadout_sub, smul_sub]
  rw [he]
  apply templateReadout_norm_of_disjoint (mul_nonneg hV hδ) s hs
  · intro i
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (hv i) (hab i) (norm_nonneg _) hV
  · intro i k
    filter_upwards [hsab i k, Lp.coeFn_smul (v i : ℂ) ((a i-b i) k)] with x hx he hnot
    change ((v i : ℂ) • ((a i-b i) k)) x = 0
    rw [he, Pi.smul_apply, hx hnot, smul_zero]

theorem weightedTemplateReadout_ideal (h : ℝ) (r : ι → Space) (v : ι → ℝ) (u : FieldL2) :
    weightedTemplateReadout v (fun i => siteInsertion h (r i) u) = idealReadout h r v u := by
  apply ContinuousLinearMap.ext
  intro f
  apply PiLp.ext
  intro i
  rw [weightedTemplateReadout_apply, idealReadout_apply]

#print axioms weightedTemplateReadout_error
#print axioms weightedTemplateReadout_ideal

end Maxwell.Continuum.FiniteAuxiliary
