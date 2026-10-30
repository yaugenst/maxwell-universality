import Maxwell.Continuum.CalibrationCellAssembly
import Maxwell.Continuum.CalibrationPowerRate

/-! The paper's explicit quadratic-in-precision torus size makes the
proved all-image operator error smaller than the requested dyadic budget. -/

noncomputable section
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.Calibration

open MasterConstants

theorem exponent_add_one_le_Cs : (exponent : ℝ)+1 ≤ Cs := by
  have hn (n : ℕ) : (n : ℝ)+1 ≤ (2 : ℝ)^n := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Nat.cast_succ, pow_succ]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
  exact hn exponent

theorem cs_mul_Cs_large : (128 : ℝ) ≤ cs*Cs := by
  have hc : (2 : ℝ)^1031 ≤ Cs := fixed_power_le_Cs (by have := exponent_large; omega)
  have he : cs*(2 : ℝ)^1031 = 128 := by
    rw [cs, show (1031 : ℕ) = 1024+7 by omega, pow_add, ← mul_assoc,
      inv_mul_cancel₀ (by positivity : (2 : ℝ)^1024 ≠ 0), one_mul]
    norm_num
  exact he ▸ mul_le_mul_of_nonneg_left hc cs_pos.le

theorem periodization_rate_large : 2*(exponent : ℝ)+20 ≤ (cs/8)*Cs^2 := by
  have hb := mul_le_mul_of_nonneg_right cs_mul_Cs_large Cs_pos.le
  have he : cs*Cs*Cs = 8*((cs/8)*Cs^2) := by ring
  rw [he] at hb
  have hx : (1 : ℝ) ≤ exponent := by exact_mod_cast (show 1 ≤ exponent by have := exponent_large; omega)
  nlinarith [exponent_add_one_le_Cs]

theorem periodization_sqrt_budget {L M : ℝ} (hL : 0 < L) (N ell : ℕ)
    (hM : Cs^4*L*((N : ℝ)+(ell : ℝ)+2)^2 ≤ M) :
    (N+20+2*exponent+10*ell : ℕ) ≤ (cs/8)*Real.sqrt (M/L) := by
  have hpos : 0 ≤ (N : ℝ)+(ell : ℝ)+2 := by positivity
  have hsq : (Cs^2*((N : ℝ)+(ell : ℝ)+2))^2 ≤ M/L := by
    apply (le_div_iff₀ hL).mpr
    convert hM using 1
    ring
  have hs : Cs^2*((N : ℝ)+(ell : ℝ)+2) ≤ Real.sqrt (M/L) :=
    (Real.le_sqrt (by positivity) (le_trans (sq_nonneg _) hsq)).mpr hsq
  have hc := periodization_rate_large
  have hc10 : (10 : ℝ) ≤ (cs/8)*Cs^2 := by linarith [show (0 : ℝ) ≤ exponent from Nat.cast_nonneg _]
  have hN := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ (cs/8)*Cs^2 by linarith)
    (Nat.cast_nonneg (α := ℝ) N)
  have hell := mul_le_mul_of_nonneg_right hc10 (Nat.cast_nonneg (α := ℝ) ell)
  have hm := mul_le_mul_of_nonneg_left hs (div_nonneg cs_pos.le (by norm_num : (0 : ℝ) ≤ 8))
  push_cast
  nlinarith

theorem periodization_error_budget {L M : ℝ} (hL : 0 < L) (N ell : ℕ)
    (hlog : L ≤ (2 : ℝ)^ell)
    (hM : Cs^4*L*((N : ℝ)+(ell : ℝ)+2)^2 ≤ M) :
    Cs^2*L^10*Real.exp (-(cs/8)*Real.sqrt (M/L)) ≤ (1/2 : ℝ)^(N+20) := by
  have hb := periodization_sqrt_budget hL N ell hM
  have he : Real.exp (-(cs/8)*Real.sqrt (M/L)) ≤
      (1/2 : ℝ)^(N+20+2*exponent+10*ell) := by
    calc
      _ ≤ Real.exp (-((N+20+2*exponent+10*ell : ℕ) : ℝ)) := by
        apply Real.exp_le_exp.mpr
        linarith
      _ = Real.exp (-1)^(N+20+2*exponent+10*ell) := by
        simpa using Real.exp_nat_mul (-1) (N+20+2*exponent+10*ell)
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_nonneg _) exp_neg_one_le_half _
  have hp : Cs^2*L^10 ≤ (2 : ℝ)^(2*exponent+10*ell) := by
    calc
      _ ≤ Cs^2*((2 : ℝ)^ell)^10 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL.le hlog 10) (sq_nonneg Cs)
      _ = _ := by rw [Cs, ← pow_mul, ← pow_mul, ← pow_add]; congr 1; omega
  calc
    _ ≤ (2 : ℝ)^(2*exponent+10*ell)*(1/2 : ℝ)^(N+20+2*exponent+10*ell) :=
      mul_le_mul hp he (Real.exp_pos _).le (by positivity)
    _ = _ := by
      rw [show N+20+2*exponent+10*ell = (N+20)+(2*exponent+10*ell) by omega,
        pow_add (1/2 : ℝ)]
      rw [mul_left_comm, ← mul_pow]
      norm_num

#print axioms periodization_error_budget

end Maxwell.Continuum.Calibration
