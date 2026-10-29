import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! A symbolic bound for the off-alias exponential error. No enormous
integer or physical discretization is constructed. -/

namespace Maxwell.Continuum.EffectiveMass

theorem power_exp_decay_le_factorial (x : ℝ) (hx : 0 ≤ x) (n : ℕ) :
    x^n * Real.exp (-x) ≤ (n.factorial : ℝ) := by
  have hn : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h := (div_le_iff₀ hn).mp (Real.pow_div_factorial_le_exp x hx n)
  calc
    _ ≤ (Real.exp x * (n.factorial : ℝ)) * Real.exp (-x) :=
      mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = (Real.exp x * Real.exp (-x)) * (n.factorial : ℝ) := by ring
    _ = (n.factorial : ℝ) := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

theorem alias_decay_majorant {h : ℝ} (hh : 0 < h) :
    (2 : ℝ)^100 * (h⁻¹)^3 * Real.exp (-1 / (512 * Real.sqrt h)) ≤ (2 : ℝ)^512 * h := by
  let x : ℝ := 1 / (512 * Real.sqrt h)
  have hs := Real.sqrt_pos.mpr hh
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hdecay := power_exp_decay_le_factorial x hx 8
  have hpow : h^4 = (Real.sqrt h)^8 := by
    calc
      _ = ((Real.sqrt h)^2)^4 := congrArg (fun y : ℝ => y^4) (Real.sq_sqrt hh.le).symm
      _ = _ := by ring
  have hscale : (h⁻¹)^3 = h * (512 : ℝ)^8 * x^8 := by
    dsimp [x]
    field_simp [hh.ne', hs.ne']
    nlinarith [hpow]
  have heq : -1 / (512 * Real.sqrt h) = -x := by dsimp [x]; ring
  rw [hscale, heq]
  calc
    _ = (2 : ℝ)^100 * h * (512 : ℝ)^8 * (x^8 * Real.exp (-x)) := by ring
    _ ≤ (2 : ℝ)^100 * h * (512 : ℝ)^8 * ((8 : ℕ).factorial : ℝ) :=
      mul_le_mul_of_nonneg_left hdecay (by positivity)
    _ = ((2 : ℝ)^100 * (512 : ℝ)^8 * ((8 : ℕ).factorial : ℝ)) * h := by ring
    _ ≤ (2 : ℝ)^188 * h := mul_le_mul_of_nonneg_right (by norm_num) hh.le
    _ ≤ (2 : ℝ)^512 * h := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : 188 ≤ 512)) hh.le

end Maxwell.Continuum.EffectiveMass
