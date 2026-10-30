import Maxwell.Cost.DyadicSqrt.Loop
import Mathlib.Data.Nat.Sqrt

/-! The existing fixed binary square-root loop computes an exact integer
square root after a power-of-four scaling. This identifies its literal
output, including perfect squares and zero. -/

namespace Maxwell.Continuum.Calibration.NaturalRoot

open Maxwell.Defect.DyadicSqrt.Integer
set_option maxHeartbeats 1800000

theorem lowerNum_bracket (A B : ℕ) (hAB : A<B) (k : ℕ) :
    B*(lowerNum A B k)^2≤A*4^k ∧ A*4^k<B*(lowerNum A B k+1)^2 := by
  induction k with
  | zero => simpa [lowerNum] using hAB
  | succ k ih =>
    have hlo := Nat.mul_le_mul_left 4 ih.1
    have hhi := Nat.mul_lt_mul_of_pos_left ih.2 (by decide : 0<4)
    rw [lowerNum]
    split_ifs with h
    · refine ⟨h,?_⟩
      rw [pow_succ (4:ℕ) k]
      nlinarith only [hhi]
    · refine ⟨?_,lt_of_not_ge h⟩
      rw [pow_succ (4:ℕ) k]
      nlinarith only [hlo]

theorem lowerNum_eq_sqrt (T k : ℕ) (hT : T<4^k) :
    lowerNum T (4^k) k=Nat.sqrt T := by
  have bounds := lowerNum_bracket T (4^k) hT k
  apply Nat.eq_sqrt'.mpr
  have hp : 0<(4:ℕ)^k := by positivity
  constructor
  · apply Nat.le_of_mul_le_mul_left (c:=4^k) ?_ hp
    simpa only [Nat.mul_comm T] using bounds.1
  · apply Nat.lt_of_mul_lt_mul_left (a:=4^k)
    simpa only [Nat.mul_comm T] using bounds.2

theorem input_lt_four_power (T : ℕ) : T<4^T.bits.length := by
  have hT : T<2^T.bits.length := by
    rw [Nat.size_eq_bits_len]
    exact Nat.lt_size_self T
  exact hT.trans_le (Nat.pow_le_pow_left (by decide : (2:ℕ)≤4) _)

theorem computed_root (T : ℕ) : lowerNum T (4^T.bits.length) T.bits.length=Nat.sqrt T :=
  lowerNum_eq_sqrt T _ (input_lt_four_power T)

#print axioms computed_root

end Maxwell.Continuum.Calibration.NaturalRoot
