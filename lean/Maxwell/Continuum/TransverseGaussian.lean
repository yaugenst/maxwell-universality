import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Convex

/-! Quantitative Gaussian moments on the literal two-dimensional transverse
plane. These estimates keep the positive damping constant symbolic. -/

noncomputable section

namespace Maxwell.Continuum.TransverseGaussian

open MeasureTheory

abbrev Plane := EuclideanSpace ℝ (Fin 2)

theorem exp_sub_le {z w : ℂ} {b : ℝ} (hz : z.re ≤ b) (hw : w.re ≤ b) :
    ‖Complex.exp z - Complex.exp w‖ ≤ Real.exp b * ‖z - w‖ := by
  apply (convex_halfSpace_re_le b).norm_image_sub_le_of_norm_deriv_le
    (fun x _ => Complex.differentiableAt_exp) ?_ hw hz
  intro x hx
  simpa only [Complex.deriv_exp, Complex.norm_exp] using Real.exp_le_exp.mpr hx

theorem gaussian_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : Plane => Real.exp (-a * ‖x‖ ^ 2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := Plane) (b := (a : ℂ)) (by exact ha) 0 0).re
  convert h using 1
  ext x
  simp only [zero_mul, add_zero]
  change Real.exp (-a * ‖x‖ ^ 2) =
    (Complex.exp (-↑a * ↑‖x‖ ^ 2)).re
  rw [← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_mul,
    ← Complex.ofReal_exp, Complex.ofReal_re]

theorem gaussian_integral {a : ℝ} (ha : 0 < a) :
    (∫ x : Plane, Real.exp (-a * ‖x‖ ^ 2)) = Real.pi / a := by
  simpa only [finrank_euclideanSpace, Fintype.card_fin,
    Nat.cast_ofNat, div_self (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_one]
    using GaussianFourier.integral_rexp_neg_mul_sq_norm (V := Plane) ha

private theorem linear_exp_bound {s : ℝ} (_hs : 0 ≤ s) :
    s ≤ Real.exp (s ^ 2 / 2) := by
  have he := Real.add_one_le_exp (s ^ 2 / 2)
  nlinarith only [he, sq_nonneg (s - 1)]

private theorem cubic_exp_bound {s : ℝ} (hs : 0 ≤ s) :
    s ^ 3 ≤ 16 * Real.exp (s ^ 2 / 2) := by
  have he' : (s ^ 2 / 2) ^ 2 / 2 ≤ Real.exp (s ^ 2 / 2) := by
    simpa only [Nat.factorial_two, Nat.cast_ofNat] using
      Real.pow_div_factorial_le_exp (s ^ 2 / 2) (show 0 ≤ s ^ 2 / 2 by positivity) 2
  have h1 : 1 ≤ Real.exp (s ^ 2 / 2) := Real.one_le_exp (by positivity)
  have h3 : s ^ 3 ≤ 1 + s ^ 4 := by
    by_cases h : s ≤ 1
    · have := pow_le_one₀ (n := 3) hs h
      nlinarith only [this, sq_nonneg (s ^ 2)]
    · have h := le_of_lt (lt_of_not_ge h)
      have hm := mul_le_mul_of_nonneg_right h (pow_nonneg hs 3)
      nlinarith only [hm]
  nlinarith only [he', h1, h3]

theorem first_moment_pointwise {a : ℝ} (ha : 0 < a) (x : Plane) :
    ‖x‖ * Real.exp (-a * ‖x‖ ^ 2) ≤
      (Real.sqrt a)⁻¹ * Real.exp (-(a / 2) * ‖x‖ ^ 2) := by
  have hs := Real.sqrt_pos.mpr ha
  have h := linear_exp_bound (mul_nonneg hs.le (norm_nonneg x))
  rw [mul_pow, Real.sq_sqrt ha.le] at h
  have hm := mul_le_mul_of_nonneg_right h (Real.exp_pos (-a * ‖x‖ ^ 2)).le
  rw [← Real.exp_add] at hm
  have he : a * ‖x‖ ^ 2 / 2 + -a * ‖x‖ ^ 2 = -(a / 2) * ‖x‖ ^ 2 := by ring
  rw [he] at hm
  apply (mul_le_mul_iff_right₀ hs).mp
  simpa only [mul_inv_cancel_left₀ hs.ne', mul_assoc] using hm

theorem third_moment_pointwise {a : ℝ} (ha : 0 < a) (x : Plane) :
    ‖x‖ ^ 3 * Real.exp (-a * ‖x‖ ^ 2) ≤
      (16 / (a * Real.sqrt a)) * Real.exp (-(a / 2) * ‖x‖ ^ 2) := by
  have hs := Real.sqrt_pos.mpr ha
  have h := cubic_exp_bound (mul_nonneg hs.le (norm_nonneg x))
  rw [mul_pow _ _ 2, Real.sq_sqrt ha.le] at h
  have hm := mul_le_mul_of_nonneg_right h (Real.exp_pos (-a * ‖x‖ ^ 2)).le
  rw [mul_assoc 16, ← Real.exp_add] at hm
  have he : a * ‖x‖ ^ 2 / 2 + -a * ‖x‖ ^ 2 = -(a / 2) * ‖x‖ ^ 2 := by ring
  rw [he, mul_pow] at hm
  have hc : Real.sqrt a ^ 3 = a * Real.sqrt a := by
    rw [pow_succ, Real.sq_sqrt ha.le]
  rw [hc] at hm
  apply (mul_le_mul_iff_right₀ (mul_pos ha hs)).mp
  calc
    a * Real.sqrt a * (‖x‖ ^ 3 * Real.exp (-a * ‖x‖ ^ 2))
        ≤ 16 * Real.exp (-(a / 2) * ‖x‖ ^ 2) := by simpa only [mul_assoc] using hm
    _ = a * Real.sqrt a * (16 / (a * Real.sqrt a) *
        Real.exp (-(a / 2) * ‖x‖ ^ 2)) := by field_simp

theorem first_moment_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : Plane => ‖x‖ * Real.exp (-a * ‖x‖ ^ 2)) := by
  apply ((gaussian_integrable (half_pos ha)).const_mul (Real.sqrt a)⁻¹).mono'
    (by fun_prop)
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (by positivity)]
    exact first_moment_pointwise ha x

theorem third_moment_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (fun x : Plane => ‖x‖ ^ 3 * Real.exp (-a * ‖x‖ ^ 2)) := by
  apply ((gaussian_integrable (half_pos ha)).const_mul (16 / (a * Real.sqrt a))).mono'
    (by fun_prop)
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (by positivity)]
    exact third_moment_pointwise ha x

theorem first_moment_integral {a : ℝ} (ha : 0 < a) :
    (∫ x : Plane, ‖x‖ * Real.exp (-a * ‖x‖ ^ 2)) ≤
      2 * Real.pi / (a * Real.sqrt a) := by
  calc
    _ ≤ ∫ x : Plane, (Real.sqrt a)⁻¹ * Real.exp (-(a / 2) * ‖x‖ ^ 2) :=
      integral_mono (first_moment_integrable ha)
        ((gaussian_integrable (half_pos ha)).const_mul _) (first_moment_pointwise ha)
    _ = _ := by rw [integral_const_mul, gaussian_integral (half_pos ha)]; ring

theorem third_moment_integral {a : ℝ} (ha : 0 < a) :
    (∫ x : Plane, ‖x‖ ^ 3 * Real.exp (-a * ‖x‖ ^ 2)) ≤
      32 * Real.pi / (a ^ 2 * Real.sqrt a) := by
  calc
    _ ≤ ∫ x : Plane, (16 / (a * Real.sqrt a)) * Real.exp (-(a / 2) * ‖x‖ ^ 2) :=
      integral_mono (third_moment_integrable ha)
        ((gaussian_integrable (half_pos ha)).const_mul _) (third_moment_pointwise ha)
    _ = _ := by rw [integral_const_mul, gaussian_integral (half_pos ha)]; ring

end Maxwell.Continuum.TransverseGaussian
