import Maxwell.Continuum.CalibrationPowerNormalize
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Symbolic iteration counts and dyadic error budgets. The large
iteration count is never enumerated by these proofs. -/

namespace Maxwell.Continuum.Calibration

def powerSteps (N : ℕ) : ℕ := 2^106*(N+200)

theorem geometric_exp_bound {δ : ℝ} (hδ : δ ≤ 1) (n : ℕ) :
    (1-δ)^n ≤ Real.exp (-δ*n) := by
  have hb : 1-δ ≤ Real.exp (-δ) := by linarith [Real.add_one_le_exp (-δ)]
  have hp := pow_le_pow_left₀ (sub_nonneg.mpr hδ) hb n
  simpa only [← Real.exp_nat_mul, mul_comm, mul_neg] using hp

theorem exp_neg_one_le_half : Real.exp (-1) ≤ (1/2 : ℝ) := by
  rw [Real.exp_neg]
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  simpa only [one_div] using
    (inv_le_inv₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 2)).mpr he

theorem powerSteps_decay (N : ℕ) :
    (1-1/(2 : ℝ)^104)^powerSteps N ≤ (1/2 : ℝ)^(N+69) := by
  have hb := geometric_exp_bound (δ := 1/(2 : ℝ)^104) (by norm_num) (powerSteps N)
  have hs : (1/(2 : ℝ)^104)*(powerSteps N : ℝ) = 4*((N : ℝ)+200) := by
    simp only [powerSteps,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_add]
    norm_num
    ring
  have hexp : -(1/(2 : ℝ)^104)*(powerSteps N : ℝ) ≤ -((N+69 : ℕ) : ℝ) := by
    rw [neg_mul, hs]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) N]
  calc
    _ ≤ Real.exp (-(1/(2 : ℝ)^104)*(powerSteps N : ℝ)) := hb
    _ ≤ Real.exp (-((N+69 : ℕ) : ℝ)) := Real.exp_le_exp.mpr hexp
    _ = Real.exp (-1)^(N+69) := by simpa using Real.exp_nat_mul (-1) (N+69)
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_nonneg _) exp_neg_one_le_half _

theorem normalized_powerSteps_decay (N : ℕ) :
    (2 : ℝ)^49*(1-1/(2 : ℝ)^104)^powerSteps N ≤ (1/2 : ℝ)^(N+20) := by
  have he : (2 : ℝ)^49*(1/2 : ℝ)^(N+69) = (1/2 : ℝ)^(N+20) := by
    have hi : N+69 = (N+20)+49 := by omega
    rw [hi,pow_add]
    ring
  exact (mul_le_mul_of_nonneg_left (powerSteps_decay N) (by positivity)).trans_eq he

/-- Enough precision to survive the actual lower norm of the unnormalized
power iterate. `extra` can be any integer with `n+1 ≤ 2^extra`. -/
def powerWorkBits (N n extra : ℕ) : ℕ := N+40*n+extra+256

theorem powerWorkBits_budget (N n extra : ℕ) (hlog : n+1 ≤ 2^extra) :
    2*((n : ℝ)+1)*(1/2 : ℝ)^powerWorkBits N n extra /
      ((1/2 : ℝ)^(48+38*n)) ≤ (1/2 : ℝ)^(N+10) := by
  have hc : (n : ℝ)+1 ≤ (2 : ℝ)^extra := by exact_mod_cast hlog
  have hpow : powerWorkBits N n extra = (48+38*n)+(N+10)+extra+(2*n+198) := by
    unfold powerWorkBits
    omega
  rw [hpow,pow_add,pow_add,pow_add]
  have hden : (1/2 : ℝ)^(48+38*n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hid : 2*((n : ℝ)+1)*
      (((1/2 : ℝ)^(48+38*n)*(1/2 : ℝ)^(N+10))*(1/2 : ℝ)^extra*(1/2 : ℝ)^(2*n+198)) /
      (1/2 : ℝ)^(48+38*n) =
      (1/2 : ℝ)^(N+10)*(2*((n : ℝ)+1)*(1/2 : ℝ)^extra*(1/2 : ℝ)^(2*n+198)) := by
    field_simp
  rw [hid]
  apply mul_le_of_le_one_right (by positivity)
  have he : ((n : ℝ)+1)*(1/2 : ℝ)^extra ≤ 1 := by
    apply (mul_le_mul_of_nonneg_right hc (by positivity)).trans_eq
    rw [← mul_pow]
    norm_num
  have hp : (1/2 : ℝ)^(2*n+198) ≤ 1/2 := by
    simpa only [pow_one] using pow_le_pow_of_le_one
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1)
      (by omega : 1 ≤ 2*n+198)
  calc
    _ = (2*(((n : ℝ)+1)*(1/2 : ℝ)^extra))*(1/2 : ℝ)^(2*n+198) := by ring
    _ ≤ (2*1)*(1/2) := mul_le_mul
      (mul_le_mul_of_nonneg_left he (by norm_num)) hp (by positivity) (by norm_num)
    _ = _ := by norm_num

#print axioms normalized_powerSteps_decay
#print axioms powerWorkBits_budget

end Maxwell.Continuum.Calibration
