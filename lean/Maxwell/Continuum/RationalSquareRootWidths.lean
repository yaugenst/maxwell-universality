import Maxwell.Continuum.RationalSquareRootEvaluation
import Maxwell.Continuum.NaturalSquareRootWidths

/-! Binary operand bounds for rational-input integer square root. The
bound is linear in input width and requested output precision. -/

namespace Maxwell.Continuum.Calibration

theorem sqrtRationalCenter_width {r : ℚ} {B : ℕ} (hr : RationalWords.Width r B) (N : ℕ) :
    RationalWords.Width (sqrtRationalCenter r N) (2*B+N+3) := by
  have hn : r.num.natAbs < 2^B := Nat.size_le.mp (by
    rw [← Nat.size_eq_bits_len]
    exact hr.num)
  have hd : r.den < 2^B := Nat.size_le.mp (by
    rw [← Nat.size_eq_bits_len]
    exact hr.den)
  have hprod : r.num.natAbs*r.den ≤ 2^(2*B) := by
    simpa only [two_mul, pow_add] using Nat.mul_le_mul hn.le hd.le
  have hp : 1 ≤ 2^(2*B) := Nat.one_le_two_pow
  have hs : r.num.natAbs*r.den+1 ≤ 2^(2*B+1) := by
    rw [pow_add, pow_one]
    omega
  have hw := (sqrtNaturalWord_bound (r.num.natAbs*r.den) N).trans
    (Nat.mul_le_mul_right (2^N) hs)
  rw [← pow_add] at hw
  have hword : (sqrtNaturalWord (r.num.natAbs*r.den) N).bits.length ≤ 2*B+N+3 := by
    rw [Nat.size_eq_bits_len]
    apply Nat.size_le.mpr
    exact hw.trans_lt (Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) (by omega))
  have hden : (2^N*r.den).bits.length ≤ 2*B+N+3 := by
    rw [Nat.size_eq_bits_len]
    apply Nat.size_le.mpr
    have hd' := Nat.mul_le_mul_left (2^N) hd.le
    rw [← pow_add] at hd'
    exact hd'.trans_lt (Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) (by omega))
  have he : sqrtRationalCenter r N =
      ((sqrtNaturalWord (r.num.natAbs*r.den) N : ℕ) : ℚ)/(2^N*r.den : ℕ) := by
    simp only [sqrtRationalCenter, sqrtNaturalCenter, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [div_div]
  rw [he]
  exact RationalWords.width_fraction (by positivity)
    (by simpa only [Int.natAbs_natCast] using hword) hden

#print axioms sqrtRationalCenter_width

end Maxwell.Continuum.Calibration
