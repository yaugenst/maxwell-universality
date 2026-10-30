import Maxwell.Continuum.WellComplex
import Mathlib.Analysis.Complex.Trigonometric

/-! Explicit analytic discs for the angular form of the literal radial profile. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Profile

open Set Metric

theorem complex_cos_sub_one {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖Complex.cos z - 1‖ ≤ ‖z‖ ^ 2 := by
  have h := Complex.cos_bound hz
  have h4 : ‖z‖ ^ 4 ≤ ‖z‖ ^ 2 := by
    nlinarith [pow_nonneg (norm_nonneg z) 2,
      mul_nonneg (sq_nonneg ‖z‖) (sub_nonneg.mpr (pow_le_one₀ (norm_nonneg z) hz (n := 2)))]
  calc
    _ = ‖(Complex.cos z - (1-z^2/2)) + (-(z^2/2))‖ := by congr 1; ring
    _ ≤ ‖Complex.cos z - (1 - z^2/2)‖ + ‖-(z^2/2)‖ := norm_add_le _ _
    _ = ‖Complex.cos z - (1 - z^2/2)‖ + ‖z‖^2/2 := by
      simp only [norm_neg, norm_div, norm_pow]; norm_num
    _ ≤ _ := by nlinarith only [h, h4, sq_nonneg ‖z‖]

theorem complex_sin_small {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖Complex.sin z‖ ≤ 2*‖z‖ := by
  have h := Complex.sin_bound hz
  have h3 : ‖z‖^3 ≤ ‖z‖ := by
    nlinarith only [mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg z) hz (n := 2)) (norm_nonneg z)]
  have h5 : ‖z‖^5 ≤ ‖z‖ := by
    nlinarith only [mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg z) hz (n := 4)) (norm_nonneg z)]
  have hp : ‖z-z^3/6‖ ≤ ‖z‖+‖z‖^3/6 := by
    have := norm_sub_le z (z^3/6)
    simpa only [norm_div, norm_pow, Complex.norm_ofNat] using this
  calc
    _ = ‖(Complex.sin z-(z-z^3/6))+(z-z^3/6)‖ := by congr 1; ring
    _ ≤ ‖Complex.sin z-(z-z^3/6)‖+‖z-z^3/6‖ := norm_add_le _ _
    _ ≤ _ := by linarith [norm_nonneg z]

theorem complex_cos_displacement (φ : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖Complex.cos ((φ : ℂ)+z)-(Real.cos φ : ℂ)‖ ≤ 3*‖z‖ := by
  have hc : ‖(Real.cos φ : ℂ)‖ ≤ 1 := by simpa only [Complex.norm_real, Real.norm_eq_abs] using Real.abs_cos_le_one φ
  have hs : ‖(Real.sin φ : ℂ)‖ ≤ 1 := by simpa only [Complex.norm_real, Real.norm_eq_abs] using Real.abs_sin_le_one φ
  have he : Complex.cos ((φ : ℂ)+z)-(Real.cos φ : ℂ) =
      (Real.cos φ : ℂ)*(Complex.cos z-1)-(Real.sin φ : ℂ)*Complex.sin z := by
    rw [Complex.cos_add, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  rw [he]
  calc
    _ ≤ ‖(Real.cos φ : ℂ)*(Complex.cos z-1)‖+‖(Real.sin φ : ℂ)*Complex.sin z‖ := norm_sub_le _ _
    _ = ‖(Real.cos φ : ℂ)‖*‖Complex.cos z-1‖+‖(Real.sin φ : ℂ)‖*‖Complex.sin z‖ := by simp only [norm_mul]
    _ ≤ 1*‖z‖^2+1*(2*‖z‖) :=
      add_le_add (mul_le_mul hc (complex_cos_sub_one hz) (norm_nonneg _) zero_le_one)
        (mul_le_mul hs (complex_sin_small hz) (norm_nonneg _) zero_le_one)
    _ ≤ _ := by nlinarith [norm_nonneg z]

def angularDenominator (φ : ℝ) (z : ℂ) : ℂ := 1-Complex.cos ((φ : ℂ)+z)

theorem angularDenominator_close (φ : ℝ) (z : ℂ)
    (hz : ‖z‖ ≤ (1-Real.cos φ)/100) :
    ‖angularDenominator φ z-((1-Real.cos φ : ℝ) : ℂ)‖ ≤ (1-Real.cos φ)/10 := by
  have hφ : 1-Real.cos φ ≤ 2 := by linarith [Real.neg_one_le_cos φ]
  have hz1 : ‖z‖ ≤ 1 := by linarith
  have he : angularDenominator φ z-((1-Real.cos φ : ℝ) : ℂ) =
      -(Complex.cos ((φ : ℂ)+z)-(Real.cos φ : ℂ)) := by
    simp only [angularDenominator, Complex.ofReal_sub, Complex.ofReal_one]
    ring
  rw [he, norm_neg]
  exact (complex_cos_displacement φ hz1).trans (by linarith [norm_nonneg z])

theorem angularDenominator_ne_zero (φ : ℝ) (hφ : Real.cos φ < 1)
    (z : ℂ) (hz : ‖z‖ ≤ (1-Real.cos φ)/100) : angularDenominator φ z ≠ 0 := by
  have h := Well.inverse_re_lower (1-Real.cos φ) (by linarith) _ (angularDenominator_close φ z hz)
  intro he
  rw [he, inv_zero, Complex.zero_re] at h
  have : 0 < 1/(2*(1-Real.cos φ)) := by positivity
  linarith

def angularComplex (φ : ℝ) (z : ℂ) : ℂ := Complex.exp (-(angularDenominator φ z)⁻¹)

theorem angularComplex_norm (φ : ℝ) (hφ : Real.cos φ < 1)
    (z : ℂ) (hz : ‖z‖ ≤ (1-Real.cos φ)/100) :
    ‖angularComplex φ z‖ ≤ Real.exp (-1/(4*(1-Real.cos φ))) := by
  have h := Well.inverse_re_lower (1-Real.cos φ) (by linarith) _ (angularDenominator_close φ z hz)
  rw [angularComplex, Complex.norm_exp, Complex.neg_re]
  apply Real.exp_le_exp.mpr
  have hp : 0 < 1/(4*(1-Real.cos φ)) := by positivity
  have he : 1/(2*(1-Real.cos φ))=2*(1/(4*(1-Real.cos φ))) := by field_simp; ring
  rw [he] at h
  rw [neg_div, one_div]
  simp only [one_div] at h hp
  linarith

theorem angularComplex_diffContOnCl (φ : ℝ) (hφ : Real.cos φ < 1) :
    DiffContOnCl ℂ (angularComplex φ) (ball (0 : ℂ) ((1-Real.cos φ)/100)) := by
  have hden : Differentiable ℂ (angularDenominator φ) := by unfold angularDenominator; fun_prop
  have hf : DifferentiableOn ℂ (angularComplex φ) (closedBall (0 : ℂ) ((1-Real.cos φ)/100)) := by
    intro z hz
    exact ((hden.differentiableAt.inv (angularDenominator_ne_zero φ hφ z (by simpa using hz))).neg).cexp.differentiableWithinAt
  refine ⟨hf.mono ball_subset_closedBall, ?_⟩
  rw [closure_ball _ (ne_of_gt (by positivity : 0 < (1-Real.cos φ)/100))]
  exact hf.continuousOn

theorem angularComplex_gevrey (φ : ℝ) (hφ : Real.cos φ < 1) (K : ℕ) :
    ‖iteratedDeriv K (angularComplex φ) 0‖ ≤ (400 : ℝ)^K*(K.factorial : ℝ)^2 := by
  apply le_trans _ (Well.cauchy_majorant_le_gevrey (1-Real.cos φ) (by linarith) K)
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le K (by positivity)
    (angularComplex_diffContOnCl φ hφ)
  intro z hz
  exact angularComplex_norm φ hφ z (mem_sphere_zero_iff_norm.mp hz).le

#print axioms angularComplex_gevrey

end Maxwell.Continuum.Profile
