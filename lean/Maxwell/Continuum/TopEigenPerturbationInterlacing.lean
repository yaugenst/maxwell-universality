import Maxwell.Continuum.TopEigenPerturbationOrder
import Maxwell.Continuum.Compression

/-! A codimension-one quadratic bound transfers to the orthogonal
complement of any normalized eigenvector above that bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.TopEigenPerturbation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem orthogonal_combination_energy (S : H →L[ℂ] H) (hS : S.IsSymmetric)
    (v f : H) (hv : ‖v‖ = 1) (l : ℝ) (he : S v = (l : ℂ) • v)
    (hf : inner ℂ v f = 0) (a b : ℂ) :
    (inner ℂ (a • f - b • v) (S (a • f - b • v))).re =
      ‖a‖ ^ 2 * (inner ℂ f (S f)).re + ‖b‖ ^ 2 * l := by
  have hfv : inner ℂ f v = 0 := inner_eq_zero_symm.mp hf
  have hsf : inner ℂ v (S f) = 0 := by
    have h : inner ℂ (S v) f = inner ℂ v (S f) := hS v f
    rw [he, inner_smul_left, hf, mul_zero] at h
    exact h.symm
  have hvv : inner ℂ v v = 1 := by rw [inner_self_eq_norm_sq_to_K, hv]; simp
  have hc : inner ℂ (a • f - b • v) (S (a • f - b • v)) =
      (starRingEnd ℂ a * a) * inner ℂ f (S f) + (starRingEnd ℂ b * b) * (l : ℂ) := by
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, inner_smul_left,
      inner_smul_right, he, hsf, hfv, hvv, mul_zero, mul_one, sub_zero, zero_sub]
    ring
  rw [hc]
  rw [RCLike.conj_mul, RCLike.conj_mul, ← RCLike.ofReal_pow, ← RCLike.ofReal_pow]
  change ((((‖a‖ ^ 2 : ℝ) : ℂ) * inner ℂ f (S f)) +
    ((‖b‖ ^ 2 : ℝ) : ℂ) * (l : ℂ)).re = _
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

omit [CompleteSpace H] in
theorem orthogonal_combination_norm (v f : H) (hv : ‖v‖ = 1)
    (hf : inner ℂ v f = 0) (a b : ℂ) :
    ‖a • f - b • v‖ ^ 2 = ‖a‖ ^ 2 * ‖f‖ ^ 2 + ‖b‖ ^ 2 := by
  have h := orthogonal_combination_energy (1 : H →L[ℂ] H)
    ContinuousLinearMap.isPositive_one.isSymmetric v f hv 1 (by simp) hf a b
  simp only [one_apply_eq_self, mul_one] at h
  have hz (x : H) : (inner ℂ x x).re = ‖x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
  simpa only [hz] using h

omit [CompleteSpace H] in
theorem upper_on_new_complement (S : H →L[ℂ] H) (hS : S.IsSymmetric)
    (u v : H) (hv : ‖v‖ = 1) (l b : ℝ) (he : S v = (l : ℂ) • v)
    (hl : b ≤ l) (hvu : inner ℂ u v ≠ 0)
    (hbound : ∀ x : H, inner ℂ u x = 0 → (inner ℂ x (S x)).re ≤ b * ‖x‖ ^ 2)
    (f : H) (hf : inner ℂ v f = 0) : (inner ℂ f (S f)).re ≤ b * ‖f‖ ^ 2 := by
  let a := inner ℂ u v
  let c := inner ℂ u f
  let x := a • f - c • v
  have hx : inner ℂ u x = 0 := by
    simp only [x, inner_sub_right, inner_smul_right, a, c]
    ring
  have h := hbound x hx
  rw [show x = a • f - c • v from rfl,
    orthogonal_combination_energy S hS v f hv l he hf,
    orthogonal_combination_norm v f hv hf] at h
  have ha : 0 < ‖a‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hvu)
  have hc : 0 ≤ ‖c‖ ^ 2 * (l - b) := mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hl)
  nlinarith

omit [CompleteSpace H] in
theorem symmetric_norm_le_of_energy (S : H →L[ℂ] H) (hS : S.IsSymmetric)
    (b : ℝ) (hb : 0 ≤ b) (h : ∀ x : H, |(inner ℂ x (S x)).re| ≤ b * ‖x‖ ^ 2) :
    ‖S‖ ≤ b := by
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient S hS]
  apply ciSup_le
  intro x
  by_cases hx : x = 0
  · subst x
    simpa [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf] using hb
  · have hn : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
    change |RCLike.re (inner ℂ (S x) x) / ‖x‖ ^ 2| ≤ b
    rw [inner_re_symm, abs_div, abs_of_nonneg hn.le]
    exact (div_le_iff₀ hn).mpr (h x)

end Maxwell.Continuum.TopEigenPerturbation
