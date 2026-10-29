import Maxwell.Continuum.WellGevrey
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-! An explicit optimization of the Gevrey integration-by-parts majorant. -/

noncomputable section

namespace Maxwell.Continuum.Well

theorem gevrey_decay_optimization (r A : ℝ) (hr : 0 < r)
    (h : ∀ K : ℕ, r ^ K * A ≤ 8 * (400 : ℝ) ^ K * (K.factorial : ℝ) ^ 2) :
    A ≤ 24 * Real.exp (-Real.sqrt r / 64) := by
  let K := ⌊Real.sqrt r / 64⌋₊
  have hK : (K : ℝ) ≤ Real.sqrt r / 64 := Nat.floor_le (by positivity)
  have hK' : Real.sqrt r / 64 - 1 < (K : ℝ) := Nat.sub_one_lt_floor _
  have hK₂ : (K : ℝ) ^ 2 ≤ r / 4096 := by
    have hh : (K : ℝ) ^ 2 ≤ (Real.sqrt r / 64) ^ 2 := by gcongr
    norm_num [div_pow, Real.sq_sqrt hr.le] at hh ⊢
    exact hh
  have hratio : 400 * (K : ℝ) ^ 2 / r ≤ 1 / 8 := by
    apply (div_le_iff₀ hr).mpr
    nlinarith
  have hfac : (K.factorial : ℝ) ≤ (K : ℝ) ^ K := by exact_mod_cast Nat.factorial_le_pow K
  have heighth : (1 / 8 : ℝ) ≤ Real.exp (-1) := by
    rw [Real.exp_neg]
    have he : Real.exp 1 ≤ (8 : ℝ) := Real.exp_one_lt_three.le.trans (by norm_num)
    simpa only [one_div] using one_div_le_one_div_of_le (Real.exp_pos 1) he
  calc
    A ≤ 8 * (400 : ℝ) ^ K * (K.factorial : ℝ) ^ 2 / r ^ K := by
      apply (le_div_iff₀ (pow_pos hr K)).mpr
      simpa only [mul_comm A] using h K
    _ ≤ 8 * (400 : ℝ) ^ K * ((K : ℝ) ^ K) ^ 2 / r ^ K := by gcongr
    _ = 8 * (400 * (K : ℝ) ^ 2 / r) ^ K := by
      rw [div_pow, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm K 2]
      ring
    _ ≤ 8 * (1 / 8 : ℝ) ^ K := by gcongr
    _ ≤ 8 * Real.exp (-1) ^ K := by gcongr
    _ = 8 * Real.exp (-(K : ℝ)) := by rw [← Real.exp_nat_mul]; congr 2; ring
    _ ≤ 8 * Real.exp (1 - Real.sqrt r / 64) := by gcongr; linarith
    _ = 8 * Real.exp 1 * Real.exp (-Real.sqrt r / 64) := by
      rw [show 1 - Real.sqrt r / 64 = 1 + (-Real.sqrt r / 64) by ring, Real.exp_add]
      ring
    _ ≤ 24 * Real.exp (-Real.sqrt r / 64) := by
      have he := Real.exp_one_lt_three.le
      nlinarith [Real.exp_pos (-Real.sqrt r / 64)]

end Maxwell.Continuum.Well
