import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-! Exact integer power ceilings and the literal first-success power
search. Their bounds use only a successful explicit candidate. -/

namespace Maxwell.Continuum.Parameters

def powerCeiling (b M : ℕ) : ℕ := b^Nat.clog b M

theorem powerCeiling_lower {b M : ℕ} (hb : 1 < b) : M ≤ powerCeiling b M :=
  Nat.le_pow_clog hb M

theorem powerCeiling_le_candidate {b M k : ℕ} (hb : 1 < b) (hk : M ≤ b^k) :
    powerCeiling b M ≤ b^k :=
  Nat.pow_le_pow_right (by omega) ((Nat.clog_le_iff_le_pow hb).mpr hk)

theorem powerCeiling_upper {b M : ℕ} (hb : 1 < b) (hM : 0 < M) :
    powerCeiling b M < b*M := by
  by_cases h1 : M ≤ 1
  · have he : M = 1 := by omega
    subst M
    simpa [powerCeiling] using hb
  · have hM1 : 1 < M := by omega
    have he := Nat.pow_pred_clog_lt_self hb hM1
    have hk : 0 < Nat.clog b M := (Nat.lt_clog_iff_pow_lt hb).mpr (by simpa using hM1)
    have hm := Nat.mul_lt_mul_of_pos_right he (by omega : 0 < b)
    have hpred : (Nat.clog b M).pred+1 = Nat.clog b M := Nat.succ_pred_eq_of_pos hk
    simpa only [← pow_succ, hpred, Nat.mul_comm, powerCeiling] using hm

theorem powerCeiling_binary_bits (M : ℕ) : (powerCeiling 2 M).bits.length = Nat.clog 2 M+1 := by
  rw [Nat.size_eq_bits_len, powerCeiling, Nat.size_pow]

theorem powerCeiling_octal_bits (M : ℕ) : (powerCeiling 8 M).bits.length = 3*Nat.clog 8 M+1 := by
  rw [Nat.size_eq_bits_len, powerCeiling, show (8 : ℕ) = 2^3 by decide, ← pow_mul, Nat.size_pow]

def firstPowerExponent (b : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∃ k : ℕ, P (b^k)) : ℕ := Nat.find hP

def firstPower (b : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∃ k : ℕ, P (b^k)) : ℕ := b^firstPowerExponent b P hP

theorem firstPower_spec (b : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∃ k : ℕ, P (b^k)) : P (firstPower b P hP) := Nat.find_spec hP

theorem firstPower_exponent_le (b : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∃ k : ℕ, P (b^k)) {k : ℕ} (hk : P (b^k)) :
    firstPowerExponent b P hP ≤ k := Nat.find_min' hP hk

theorem firstPower_le_candidate {b : ℕ} (hb : 1 ≤ b) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∃ k : ℕ, P (b^k)) {k : ℕ} (hk : P (b^k)) : firstPower b P hP ≤ b^k :=
  Nat.pow_le_pow_right hb (firstPower_exponent_le b P hP hk)

theorem firstPower_prior_fails (b : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∃ k : ℕ, P (b^k)) {k : ℕ} (hk : k < firstPowerExponent b P hP) :
    ¬P (b^k) := Nat.find_min hP hk

theorem firstPower_eventual_exists {b : ℕ} (hb : 1 < b) (P : ℕ → Prop)
    {M : ℕ} (hP : ∀ n, M ≤ n → P n) : ∃ k : ℕ, P (b^k) :=
  ⟨Nat.clog b M, hP _ (Nat.le_pow_clog hb M)⟩

theorem firstPower_binary_bits (P : ℕ → Prop) [DecidablePred P]
    (hP : ∃ k : ℕ, P (2^k)) :
    (firstPower 2 P hP).bits.length = firstPowerExponent 2 P hP+1 := by
  rw [Nat.size_eq_bits_len, firstPower, Nat.size_pow]

end Maxwell.Continuum.Parameters
