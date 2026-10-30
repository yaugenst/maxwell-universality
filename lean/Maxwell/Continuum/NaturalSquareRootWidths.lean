import Maxwell.Continuum.NaturalSquareRootEvaluation
import Maxwell.Continuum.RationalFiniteWidths

/-! Word bounds for the scaled integer-square-root evaluator. -/

namespace Maxwell.Continuum.Calibration

theorem sqrtNaturalCenter_width (n N : ℕ) :
    RationalWords.Width (sqrtNaturalCenter n N) (n+N+3) := by
  have hw := sqrtNaturalWord_bound n N
  have hn : n+1≤2^(n+1) := (Nat.lt_two_pow_self (n := n+1)).le
  have hh : sqrtNaturalWord n N≤2^(n+1+N) := by
    exact hw.trans ((Nat.mul_le_mul_right (2^N) hn).trans_eq (pow_add 2 (n+1) N).symm)
  have hb : (sqrtNaturalWord n N).bits.length≤n+N+3 := by
    rw [Nat.size_eq_bits_len]
    apply Nat.size_le.mpr
    apply hh.trans_lt
    exact Nat.pow_lt_pow_right (by decide : 1<(2 : ℕ)) (by omega)
  have hd : (2^N).bits.length≤n+N+3 := by
    rw [Nat.size_eq_bits_len,Nat.size_pow]
    omega
  have h := RationalWords.width_fraction (z := (sqrtNaturalWord n N : ℤ)) (d := 2^N)
    (by positivity) (by simpa only [Int.natAbs_natCast] using hb) hd
  simpa only [sqrtNaturalCenter,Int.cast_natCast,Nat.cast_pow,Nat.cast_ofNat] using h

#print axioms sqrtNaturalCenter_width

end Maxwell.Continuum.Calibration
