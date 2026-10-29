import Maxwell.Continuum.WellKernelConstants
import Maxwell.Continuum.WellKernelLower
import Mathlib.Analysis.Complex.ExponentialBounds

/-! A fixed, quantitative minorization of the actual Green kernel on
differences of points in the unit ball. -/

noncomputable section

namespace Maxwell.Continuum.Well

open scoped NNReal

theorem heat_time_exp_lower (ρ : ℝ) (_hρ : 0 < ρ) (hρu : ρ ≤ 1 / 4) :
    (1 / 16 : ℝ) ≤ Real.exp (-2 * ρ - 2) := by
  have hhalf : Real.exp (2 * ρ) ≤ 2 := by
    have he : Real.exp (2 * ρ) ^ 2 = Real.exp (4 * ρ) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hle := Real.exp_le_exp.mpr (show 4 * ρ ≤ 1 by linarith)
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos (2 * ρ)]
  have htwo : Real.exp 2 ≤ 8 := by
    have he : Real.exp 2 = Real.exp 1 ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      norm_num
    rw [he]
    have hle : Real.exp 1 ≤ 11 / 4 := by linarith [Real.exp_one_lt_d9]
    nlinarith [Real.exp_pos 1]
  have hexp : Real.exp (2 * ρ + 2) ≤ 16 := by
    rw [Real.exp_add]
    nlinarith [mul_le_mul hhalf htwo (Real.exp_pos 2).le (by norm_num : (0 : ℝ) ≤ 2)]
  rw [show -2 * ρ - 2 = -(2 * ρ + 2) by ring, Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (Real.exp_pos _) hexp

theorem heat_time_power_lower (ρ : ℝ) (hρ : 0 < ρ) :
    (4 * Real.sqrt ρ ^ 3)⁻¹ ≤ (2 * ρ) ^ (-3 / 2 : ℝ) := by
  have hs : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have htwo : Real.sqrt (2 : ℝ) ^ 3 ≤ 4 := by
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hroot : Real.sqrt (2 : ℝ) ≤ 2 := by
      nlinarith [Real.sqrt_nonneg (2 : ℝ)]
    rw [pow_succ, hsq]
    linarith
  have he : (2 * ρ) ^ (3 / 2 : ℝ) = Real.sqrt (2 * ρ) ^ 3 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (by positivity)]
    norm_num
  have hp : (2 * ρ) ^ (3 / 2 : ℝ) ≤ 4 * Real.sqrt ρ ^ 3 := by
    rw [he, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), mul_pow]
    exact mul_le_mul_of_nonneg_right htwo (by positivity)
  rw [show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by ring, Real.rpow_neg (by positivity)]
  exact inv_le_inv₀ (by positivity) (by positivity) |>.mpr hp

theorem resolventKernel_quantitative_lower (a : Fin 3 → ℝ≥0) (ha : ∀ i, a i ≠ 0)
    (ρ : ℝ) (hρ : 0 < ρ) (hρu : ρ ≤ 1 / 4)
    (hal : ∀ i, (2 * ρ)⁻¹ ≤ (a i : ℝ))
    (hau : ∀ i, (a i : ℝ) ≤ 256 / ρ)
    (x : Space) (hx : x ≠ 0) (hxu : ‖x‖ ≤ 2) :
    ρ / (2 : ℝ) ^ 24 ≤ resolventKernel a x := by
  have hs : 0 < Real.sqrt ρ := Real.sqrt_pos.mpr hρ
  have hR := heatRadiusSq_upper a ((2 * ρ)⁻¹) (by positivity) hal x
  have hR' : heatRadiusSq a x ≤ 2 * ρ := by
    have he : ‖x‖ ^ 2 / (4 * (2 * ρ)⁻¹) = ρ * ‖x‖ ^ 2 / 2 := by
      field_simp
      ring
    rw [he] at hR
    have hnorm : ‖x‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg x]
    nlinarith
  have hlo := resolventKernel_interval_lower a ha x hx ρ (2 * ρ) hρ hR'
  have hc := heatPrefactor_numeric_lower a ha ρ hρ hau
  have ht := heat_time_power_lower ρ hρ
  have he := heat_time_exp_lower ρ hρ hρu
  have hp := heatPrefactor_nonneg a
  have hdiv : 2 * ρ / ρ = 2 := by field_simp
  rw [hdiv] at hlo
  apply le_trans _ hlo
  calc
    _ = ρ * (Real.sqrt ρ ^ 3 / (2 : ℝ) ^ 18) *
        (4 * Real.sqrt ρ ^ 3)⁻¹ * (1 / 16) := by field_simp; ring
    _ ≤ ρ * heatPrefactor a * (2 * ρ) ^ (-3 / 2 : ℝ) * Real.exp (-2 * ρ - 2) := by
      apply mul_le_mul _ he (by norm_num) (by positivity)
      apply mul_le_mul _ ht (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hc hρ.le

end Maxwell.Continuum.Well
