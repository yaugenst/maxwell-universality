import Maxwell.Continuum.MasterConstants
import Mathlib.Data.Nat.Factorial.Basic

/-! The explicit arithmetic at the end of the continuum majorant ledger.
This verifies the factorial/power envelope itself; analytic estimates
must still be proved separately before being bounded by this envelope. -/

noncomputable section

namespace Maxwell.Continuum.MasterConstants

def Mstar : ℝ := (2 : ℝ)^16384

def derivativeEnvelope (j : ℕ) : ℝ := (j.factorial : ℝ)^4 * Mstar^((j+1)^2)

theorem derivativeEnvelope_nonneg (j : ℕ) : 0 ≤ derivativeEnvelope j := by
  unfold derivativeEnvelope Mstar
  positivity

theorem factorial32_le_power : ((32 : ℕ).factorial : ℝ) ≤ (2 : ℝ)^160 := by
  calc
    _ ≤ (32 : ℝ)^32 := by exact_mod_cast Nat.factorial_le_pow 32
    _ = (2 : ℝ)^160 := by
      rw [show (32 : ℝ) = 2^5 by norm_num, ← pow_mul]

theorem envelope32_le_power : derivativeEnvelope 32 ≤ (2 : ℝ)^(640+16384*33^2) := by
  have hf := pow_le_pow_left₀ (show (0:ℝ) ≤ ((32:ℕ).factorial:ℝ) by positivity)
    factorial32_le_power 4
  unfold derivativeEnvelope Mstar
  change ((32:ℕ).factorial:ℝ)^4 * ((2:ℝ)^16384)^(33^2) ≤ _
  calc
    _ ≤ ((2 : ℝ)^160)^4 * ((2:ℝ)^16384)^(33^2) :=
      mul_le_mul_of_nonneg_right hf (by positivity)
    _ = _ := by rw [← pow_mul, ← pow_mul, ← pow_add]

theorem ledger_power_bound :
    derivativeEnvelope 32 ^ 1024 < (2 : ℝ)^((2 : ℕ)^35) := by
  calc
    _ ≤ ((2 : ℝ)^(640+16384*33^2))^1024 :=
      pow_le_pow_left₀ (derivativeEnvelope_nonneg 32) envelope32_le_power 1024
    _ = (2 : ℝ)^((640+16384*33^2)*1024) := (pow_mul _ _ _).symm
    _ < _ := pow_lt_pow_right₀ (by norm_num) (by norm_num)

theorem ledger_below_master : derivativeEnvelope 32 ^ 1024 < Cs := by
  refine ledger_power_bound.trans ?_
  apply pow_lt_pow_right₀ (by norm_num)
  norm_num [exponent]

theorem length_upper_bound : Ls < 8 * Cs^64 := by
  have hc := Nat.ceil_lt_add_one (show (0:ℝ) ≤ (64 * (exponent:ℝ))/3 by positivity)
  change (lengthExponent:ℝ) < (64 * (exponent:ℝ))/3 + 1 at hc
  have hn : 3 * lengthExponent < 3 + exponent * 64 := by
    exact_mod_cast (show (3:ℝ) * lengthExponent < 3 + (exponent:ℝ)*64 by linarith)
  rw [Ls_eq_two_pow, Cs, ← pow_mul, show (8:ℝ)=2^3 by norm_num, ← pow_add]
  exact pow_lt_pow_right₀ (by norm_num) hn

#print axioms ledger_below_master
#print axioms length_upper_bound

end Maxwell.Continuum.MasterConstants
