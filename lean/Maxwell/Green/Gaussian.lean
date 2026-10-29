import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # The transverse two-dimensional Gaussian coefficient -/

open MeasureTheory Real

namespace Maxwell.Green

/-- The transverse Gaussian factor, before diagonalization-independent
reassembly of its determinant. -/
theorem integral_gaussian_two (a b : ℝ) :
    (∫ w : ℝ × ℝ, exp (-a * w.1 ^ 2 - b * w.2 ^ 2)) =
      sqrt (π / a) * sqrt (π / b) := by
  calc
    (∫ w : ℝ × ℝ, exp (-a * w.1 ^ 2 - b * w.2 ^ 2)) =
        ∫ w : ℝ × ℝ, exp (-a * w.1 ^ 2) * exp (-b * w.2 ^ 2) := by
      congr 1
      funext w
      rw [← exp_add]
      congr 1
      ring
    _ = (∫ x : ℝ, exp (-a * x ^ 2)) * (∫ y : ℝ, exp (-b * y ^ 2)) :=
      by simpa only [Measure.volume_eq_prod] using
        (integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
          (fun x => exp (-a * x ^ 2)) (fun y => exp (-b * y ^ 2)))
    _ = sqrt (π / a) * sqrt (π / b) := by rw [integral_gaussian, integral_gaussian]

/-- For positive transverse eigenvalues, the coefficient is π divided by
the square root of their product. -/
theorem integral_gaussian_two_pos {a b : ℝ} (ha : 0 < a) (_hb : 0 < b) :
    (∫ w : ℝ × ℝ, exp (-a * w.1 ^ 2 - b * w.2 ^ 2)) =
      π / sqrt (a * b) := by
  rw [integral_gaussian_two, sqrt_div pi_pos.le, sqrt_div pi_pos.le,
    sqrt_mul ha.le]
  rw [div_mul_div_comm, mul_self_sqrt pi_pos.le]

/-- The exact two-dimensional Gaussian integral in the pole chart.
`q₁*q₂` is the determinant in an orthonormal eigenbasis. -/
theorem transverse_gaussian_integral {T c q₁ q₂ : ℝ}
    (hT : 0 < T) (hc : 0 < c) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) :
    (∫ w : ℝ × ℝ,
      exp (-(T / (2 * c)) * (q₁ * w.1 ^ 2 + q₂ * w.2 ^ 2))) =
        2 * π * c / (T * sqrt (q₁ * q₂)) := by
  have hs : 0 < T / (2 * c) := div_pos hT (mul_pos (by norm_num) hc)
  have heq : (fun w : ℝ × ℝ =>
      exp (-(T / (2 * c)) * (q₁ * w.1 ^ 2 + q₂ * w.2 ^ 2))) =
      fun w => exp (-(T / (2 * c) * q₁) * w.1 ^ 2 -
        (T / (2 * c) * q₂) * w.2 ^ 2) := by
    funext w
    congr 1
    ring
  rw [heq, integral_gaussian_two_pos (mul_pos hs hq₁) (mul_pos hs hq₂)]
  have hmul : (T / (2 * c) * q₁) * (T / (2 * c) * q₂) =
      (T / (2 * c)) ^ 2 * (q₁ * q₂) := by ring
  rw [hmul, sqrt_mul (sq_nonneg _), sqrt_sq hs.le]
  field_simp

/-- The same transverse coefficient in the complex-plane representation of
two-dimensional Lebesgue measure used for the absolute error estimates. -/
theorem transverse_gaussian_integral_complex_domain {T c q₁ q₂ : ℝ}
    (hT : 0 < T) (hc : 0 < c) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) :
    (∫ w : ℂ,
      exp (-(T / (2 * c)) * (q₁ * w.re ^ 2 + q₂ * w.im ^ 2))) =
        2 * π * c / (T * sqrt (q₁ * q₂)) := by
  calc
    _ = ∫ w : ℝ × ℝ,
        exp (-(T / (2 * c)) * (q₁ * w.1 ^ 2 + q₂ * w.2 ^ 2)) := by
      simpa only [Complex.measurableEquivRealProd_apply] using
        Complex.volume_preserving_equiv_real_prod.integral_comp'
          (fun w : ℝ × ℝ =>
            exp (-(T / (2 * c)) * (q₁ * w.1 ^ 2 + q₂ * w.2 ^ 2)))
    _ = _ := transverse_gaussian_integral hT hc hq₁ hq₂

/-- The residue factor and Fourier normalization cancel the longitudinal
speed exactly, leaving the stated leading scalar coefficient. -/
theorem residue_gaussian_coefficient {A c T D : ℂ} (hc : c ≠ 0)
    (hT : T ≠ 0) (hD : D ≠ 0) :
    (1 / (2 * (π : ℂ)) ^ 3) * (2 * (π : ℂ) * Complex.I) *
      ((A / (Complex.I * c)) * (2 * (π : ℂ) * c / (T * D))) =
        A / (2 * (π : ℂ) * T * D) := by
  have hp : (π : ℂ) ≠ 0 := by exact_mod_cast pi_pos.ne'
  field_simp

end Maxwell.Green
