import Maxwell.Continuum.SquareRootStability
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Module

/-! Stability of a normalized rectangular reconstruction, with explicit
inverse-square-root constants on the actual effective-mass window. -/

noncomputable section
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum

theorem inv_sqrt_window_bound {a : ℝ} (ha : 1 / (2 : ℝ)^128 ≤ a) :
    (Real.sqrt a)⁻¹ ≤ (2 : ℝ)^200 := by
  have hl : 1 / (2 : ℝ)^64 ≤ Real.sqrt a := by
    apply Real.le_sqrt_of_sq_le
    convert ha using 1
    norm_num
  have hp : 0 < Real.sqrt a := lt_of_lt_of_le (by positivity) hl
  have hi := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 1 / 2^64) hl
  norm_num at hi ⊢
  linarith

theorem inv_sqrt_window_lipschitz {a b : ℝ}
    (ha : 1 / (2 : ℝ)^128 ≤ a) (hb : 1 / (2 : ℝ)^128 ≤ b) :
    |(Real.sqrt a)⁻¹ - (Real.sqrt b)⁻¹| ≤ (2 : ℝ)^200 * |a-b| := by
  have hap : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hbp : 0 < b := lt_of_lt_of_le (by positivity) hb
  have hsa : 1 / (2 : ℝ)^64 ≤ Real.sqrt a := by
    apply Real.le_sqrt_of_sq_le
    convert ha using 1
    norm_num
  have hsb : 1 / (2 : ℝ)^64 ≤ Real.sqrt b := by
    apply Real.le_sqrt_of_sq_le
    convert hb using 1
    norm_num
  have hd : 1 / (2 : ℝ)^192 ≤ Real.sqrt a * Real.sqrt b * (Real.sqrt a + Real.sqrt b) := by
    have h1 := mul_le_mul hsa hsb (by positivity) (Real.sqrt_nonneg a)
    have h2 := mul_le_mul h1 (hsa.trans (le_add_of_nonneg_right (Real.sqrt_nonneg b)))
      (by positivity) (mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b))
    convert h2 using 1
    norm_num
  rw [inv_sqrt_sub_abs hap hbp]
  calc
    _ ≤ |a-b| / (1 / (2 : ℝ)^192) :=
      div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hd
    _ ≤ _ := by norm_num; nlinarith [abs_nonneg (a-b)]

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup Y] [NormedSpace ℂ Y]

theorem normalized_image_error (A C : X →L[ℂ] Y) (u v : X)
    {a b : ℝ} (ha : 0 < a) :
    ‖((Real.sqrt a)⁻¹ : ℂ) • A u - ((Real.sqrt b)⁻¹ : ℂ) • C v‖ ≤
      (Real.sqrt a)⁻¹ * (‖A‖ * ‖u-v‖ + ‖A-C‖ * ‖v‖) +
        |(Real.sqrt a)⁻¹ - (Real.sqrt b)⁻¹| * ‖C v‖ := by
  have he : ((Real.sqrt a)⁻¹ : ℂ) • A u - ((Real.sqrt b)⁻¹ : ℂ) • C v =
      ((Real.sqrt a)⁻¹ : ℂ) • (A (u-v) + (A-C) v) +
        (((Real.sqrt a)⁻¹ : ℂ) - ((Real.sqrt b)⁻¹ : ℂ)) • C v := by
    simp only [map_sub, sub_apply]
    module
  rw [he]
  apply (norm_add_le _ _).trans
  simp only [norm_smul]
  have hn : ‖((Real.sqrt a)⁻¹ : ℂ)‖ = (Real.sqrt a)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg a)]
  have hd : ‖(((Real.sqrt a)⁻¹ : ℂ) - ((Real.sqrt b)⁻¹ : ℂ))‖ =
      |(Real.sqrt a)⁻¹ - (Real.sqrt b)⁻¹| := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_inv, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
  rw [hn, hd]
  refine add_le_add ?_ le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_add_le _ _).trans (add_le_add (A.le_opNorm _) ((A-C).le_opNorm _))

end Maxwell.Continuum
