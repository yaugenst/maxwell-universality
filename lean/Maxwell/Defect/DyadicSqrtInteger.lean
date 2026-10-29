import Maxwell.Defect.DyadicSqrt
import Mathlib.Data.Nat.Size

/-! Integer implementation of the rational square-root bisection. The
comparison clears positive denominators exactly, and all intermediate
numerators have explicit binary-length bounds. -/

namespace Maxwell.Defect.DyadicSqrt.Integer

def lowerNum (A B : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
      if B * (2 * lowerNum A B k + 1) ^ 2 ≤ A * 4 ^ (k + 1)
      then 2 * lowerNum A B k + 1 else 2 * lowerNum A B k

/-- The finite bisection lower numerator always remains strictly below
its dyadic denominator, including when the input is exactly one. -/
theorem lowerNum_lt_pow_two (A B k : ℕ) : lowerNum A B k < 2 ^ k := by
  induction k with
  | zero => simp [lowerNum]
  | succ k ih =>
    rw [lowerNum, pow_succ]
    split_ifs <;> omega

theorem lowerNum_bits_length_le (A B k : ℕ) : (lowerNum A B k).bits.length ≤ k := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr (lowerNum_lt_pow_two A B k)

theorem upperNum_bits_length_le (A B k : ℕ) :
    (lowerNum A B k + 1).bits.length ≤ k + 1 := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  have h := lowerNum_lt_pow_two A B k
  have hp : 0 < 2 ^ k := by positivity
  rw [pow_succ]
  omega

theorem trialNum_lt_pow_two (A B k : ℕ) :
    2 * lowerNum A B k + 1 < 2 ^ (k + 1) := by
  have h := lowerNum_lt_pow_two A B k
  rw [pow_succ]
  omega

theorem trialNum_bits_length_le (A B k : ℕ) :
    (2 * lowerNum A B k + 1).bits.length ≤ k + 1 := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr (trialNum_lt_pow_two A B k)

theorem four_pow_eq_two_pow (k : ℕ) : (4 : ℕ) ^ k = 2 ^ (2 * k) := by
  rw [pow_mul]
  norm_num

theorem scaledNumerator_bits_length_le (A k : ℕ) :
    (A * 4 ^ k).bits.length ≤ A.bits.length + 2 * k := by
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  rw [four_pow_eq_two_pow, pow_add]
  exact Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self A) (by positivity)

theorem comparisonLeft_bits_length_le (A B k : ℕ) :
    (B * (2 * lowerNum A B k + 1) ^ 2).bits.length ≤ B.bits.length + 2 * (k + 1) := by
  rw [Nat.size_eq_bits_len, Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  have hsq : (2 * lowerNum A B k + 1) ^ 2 < 2 ^ (2 * (k + 1)) := by
    rw [Nat.mul_comm 2 (k + 1), pow_mul]
    exact Nat.pow_lt_pow_left (trialNum_lt_pow_two A B k) (by decide)
  rw [pow_add]
  exact (Nat.mul_le_mul_left B hsq.le).trans_lt
    (Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self B) (by positivity))

/-- The integer branch test is exactly the rational midpoint test. -/
theorem midpoint_test_iff (A B n k : ℕ) (hB : 0 < B) :
    (((2 * n + 1 : ℕ) : ℚ) / 2 ^ (k + 1)) ^ 2 ≤ (A : ℚ) / B ↔
      B * (2 * n + 1) ^ 2 ≤ A * 4 ^ (k + 1) := by
  have hBq : (0 : ℚ) < B := by exact_mod_cast hB
  rw [div_pow, div_le_div_iff₀ (by positivity : (0 : ℚ) < (2 ^ (k + 1)) ^ 2) hBq]
  have hp : ((2 : ℚ) ^ (k + 1)) ^ 2 = 4 ^ (k + 1) := by
    rw [← pow_mul, Nat.mul_comm (k + 1) 2, pow_mul]
    norm_num
  rw [hp]
  norm_cast
  rw [Nat.mul_comm ((2 * n + 1) ^ 2) B]

private theorem midpoint_identity (n k : ℕ) :
    (((n : ℚ) / 2 ^ k + ((n + 1 : ℕ) : ℚ) / 2 ^ k) / 2) =
      ((2 * n + 1 : ℕ) : ℚ) / 2 ^ (k + 1) := by
  push_cast
  rw [pow_succ]
  field_simp
  ring

/-- Both exact endpoints are represented by adjacent integer numerators.
The identity holds for every numerator when the denominator is positive. -/
theorem interval_binding (A B k : ℕ) (hB : 0 < B) :
    interval ((A : ℚ) / B) k =
      ((lowerNum A B k : ℚ) / 2 ^ k, ((lowerNum A B k + 1 : ℕ) : ℚ) / 2 ^ k) := by
  induction k with
  | zero => simp [interval, lowerNum]
  | succ k ih =>
    rw [interval, step, ih]
    dsimp only
    rw [midpoint_identity]
    by_cases hc : B * (2 * lowerNum A B k + 1) ^ 2 ≤ A * 4 ^ (k + 1)
    · have hq := (midpoint_test_iff A B (lowerNum A B k) k hB).mpr hc
      simp only [hq, ite_true, lowerNum, hc]
      apply Prod.ext
      · rfl
      · push_cast
        rw [pow_succ]
        field_simp
        ring
    · have hq : ¬ (((2 * lowerNum A B k + 1 : ℕ) : ℚ) / 2 ^ (k + 1)) ^ 2 ≤
          (A : ℚ) / B := fun h => hc ((midpoint_test_iff A B (lowerNum A B k) k hB).mp h)
      simp only [hq, ite_false, lowerNum, hc]
      apply Prod.ext
      · push_cast
        rw [pow_succ]
        field_simp
      · rfl

theorem lower_binding (A B k : ℕ) (hB : 0 < B) :
    (lowerNum A B k : ℚ) / 2 ^ k = lower ((A : ℚ) / B) k := by
  rw [lower, interval_binding A B k hB]

theorem upper_binding (A B k : ℕ) (hB : 0 < B) :
    ((lowerNum A B k + 1 : ℕ) : ℚ) / 2 ^ k = upper ((A : ℚ) / B) k := by
  rw [upper, interval_binding A B k hB]

end Maxwell.Defect.DyadicSqrt.Integer
