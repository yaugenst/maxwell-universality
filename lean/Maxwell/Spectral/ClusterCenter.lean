import Maxwell.Spectral.SeparatedInverse
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

namespace Maxwell.Spectral.ClusterCenter

noncomputable section

variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable [FiniteDimensional ℂ H]

theorem shifted_quadratic (T : H →L[ℂ] H) (hT : T.toLinearMap.IsSymmetric)
    (E : ℝ) (v : H) :
    Complex.re (inner ℂ v (SeparatedInverse.shifted T E v)) =
      ∑ i, (hT.eigenvalues rfl i - E) * ‖(hT.eigenvectorBasis rfl).repr v i‖ ^ 2 := by
  have hn : ∑ i, ‖(hT.eigenvectorBasis rfl).repr v i‖ ^ 2 = ‖v‖ ^ 2 := by
    simpa only [OrthonormalBasis.repr_apply_apply] using
      (hT.eigenvectorBasis rfl).sum_sq_norm_inner_right v
  change Complex.re (inner ℂ v (T v - (E : ℂ) • v)) = _
  rw [inner_sub_right, inner_smul_right, Complex.sub_re, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hv : Complex.re (inner ℂ v v) = ‖v‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm
  rw [hv]
  have hq := spectral_quadratic_form hT v
  change Complex.re (inner ℂ v (T v)) = _ at hq
  rw [hq, ← hn, Finset.mul_sum]
  simp only [sub_mul, Finset.sum_sub_distrib]

/-- On an exact spectral cluster in `[E,E+δ]`, the shifted residual square
is bounded by `δ` times its positive quadratic form. -/
theorem shifted_polynomial_on_window (T : H →L[ℂ] H)
    (hT : T.toLinearMap.IsSymmetric) (E δ : ℝ) (v : H)
    (hwindow : ∀ i, (hT.eigenvectorBasis rfl).repr v i ≠ 0 →
      0 ≤ hT.eigenvalues rfl i - E ∧ hT.eigenvalues rfl i - E ≤ δ) :
    0 ≤ Complex.re (inner ℂ v (SeparatedInverse.shifted T E v)) ∧
      ‖SeparatedInverse.shifted T E v‖ ^ 2 ≤
        δ * Complex.re (inner ℂ v (SeparatedInverse.shifted T E v)) := by
  rw [shifted_quadratic T hT E v]
  constructor
  · apply Finset.sum_nonneg
    intro i _
    by_cases hi : (hT.eigenvectorBasis rfl).repr v i = 0
    · simp [hi]
    · exact mul_nonneg (hwindow i hi).1 (sq_nonneg _)
  · have hres := shifted_norm_sq_spectral T.toLinearMap hT E v
    change ‖SeparatedInverse.shifted T E v‖ ^ 2 = _ at hres
    rw [hres, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : (hT.eigenvectorBasis rfl).repr v i = 0
    · simp [hi]
    · have hw := hwindow i hi
      have hm := mul_le_mul_of_nonneg_right hw.2 hw.1
      have hh := mul_le_mul_of_nonneg_right hm
        (sq_nonneg ‖(hT.eigenvectorBasis rfl).repr v i‖)
      nlinarith only [hh]

theorem shifted_norm_on_window (T : H →L[ℂ] H)
    (hT : T.toLinearMap.IsSymmetric) (E δ : ℝ) (hδ : 0 ≤ δ) (v : H)
    (hwindow : ∀ i, (hT.eigenvectorBasis rfl).repr v i ≠ 0 →
      0 ≤ hT.eigenvalues rfl i - E ∧ hT.eigenvalues rfl i - E ≤ δ) :
    ‖SeparatedInverse.shifted T E v‖ ≤ δ * ‖v‖ := by
  have hres := shifted_norm_sq_spectral T.toLinearMap hT E v
  change ‖SeparatedInverse.shifted T E v‖ ^ 2 = _ at hres
  have hn : ∑ i, ‖(hT.eigenvectorBasis rfl).repr v i‖ ^ 2 = ‖v‖ ^ 2 := by
    simpa only [OrthonormalBasis.repr_apply_apply] using
      (hT.eigenvectorBasis rfl).sum_sq_norm_inner_right v
  have hs : ‖SeparatedInverse.shifted T E v‖ ^ 2 ≤ δ ^ 2 * ‖v‖ ^ 2 := by
    rw [hres, ← hn, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : (hT.eigenvectorBasis rfl).repr v i = 0
    · simp [hi]
    · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact pow_le_pow_left₀ (hwindow i hi).1 (hwindow i hi).2 2
  nlinarith only [hs, norm_nonneg (SeparatedInverse.shifted T E v), mul_nonneg hδ (norm_nonneg v)]

variable [CompleteSpace H] [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Exact cluster location implies both center premises of the local
spectral-polynomial certificate. They do not need separate numerical tests. -/
theorem trial_center_bounds (T : H →L[ℂ] H) (hT : T.toLinearMap.IsSymmetric)
    (Φ : V →L[ℂ] H) (E δ b : ℝ) (hδ : 0 ≤ δ) (hδb : δ ≤ b - E)
    (hΦ : ‖Φ‖ ≤ 1)
    (hwindow : ∀ x i, (hT.eigenvectorBasis rfl).repr (Φ x) i ≠ 0 →
      0 ≤ hT.eigenvalues rfl i - E ∧ hT.eigenvalues rfl i - E ≤ δ) :
    ‖(SeparatedInverse.shifted T E).comp Φ‖ ≤ δ ∧
      ∀ x, ‖(SeparatedInverse.shifted T E).comp Φ x‖ ^ 2 ≤
        (b - E) * Complex.re (inner ℂ x (Φ.adjoint.comp ((SeparatedInverse.shifted T E).comp Φ) x)) := by
  constructor
  · apply ((SeparatedInverse.shifted T E).comp Φ).opNorm_le_bound hδ
    intro x
    have hn := (Φ.le_opNorm x).trans (mul_le_mul_of_nonneg_right hΦ (norm_nonneg x))
    calc
      _ ≤ δ * ‖Φ x‖ := shifted_norm_on_window T hT E δ hδ (Φ x) (hwindow x)
      _ ≤ δ * (1 * ‖x‖) := mul_le_mul_of_nonneg_left hn hδ
      _ = _ := by ring
  · intro x
    have h := shifted_polynomial_on_window T hT E δ (Φ x) (hwindow x)
    have hh := h.2.trans (mul_le_mul_of_nonneg_right hδb h.1)
    simpa only [ContinuousLinearMap.comp_apply, Φ.adjoint_inner_right] using hh

end
end Maxwell.Spectral.ClusterCenter
