import Maxwell.Defect.RationalNormalizeScale

/-! Exact integer norm and output-pair formulas for the bounded
normalization machine. No rational vector division is required internally. -/
namespace Maxwell.Defect
open scoped BigOperators
variable {n : ℕ}

def integerNormSq (y : Fin n → ℤ) : ℕ := ∑ i, (y i).natAbs ^ 2

theorem integerNormSq_cast (y : Fin n → ℤ) :
    (integerNormSq y : ℚ) = rationalNormSq (fun i => (y i : ℚ)) := by
  simp only [integerNormSq, rationalNormSq, Nat.cast_sum, Nat.cast_pow]
  apply Finset.sum_congr rfl
  intro i _
  have hh : ((y i).natAbs : ℤ)^2 = y i ^ 2 := by rw [Int.natCast_natAbs, sq_abs]
  have hh' := congrArg (fun z : ℤ => (z : ℚ)) hh
  simpa only [Int.cast_pow, Int.cast_natCast] using hh'

theorem integerNormSq_pos (y : Fin n → ℤ) (hy : y ≠ 0) : 0 < integerNormSq y := by
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hy (funext hh)
  apply Finset.sum_pos' (fun _ _ => Nat.zero_le _)
  exact ⟨i, Finset.mem_univ _, pow_pos (Int.natAbs_pos.mpr hi) 2⟩

theorem integer_normalization_ratio (y : Fin n → ℤ) (Bnum Bden : ℕ) :
    rationalNormSq (fun i => (y i : ℚ)) / ((Bnum : ℚ) / (Bden : ℚ))^2 =
      ((integerNormSq y * Bden^2 : ℕ) : ℚ) / (Bnum : ℚ)^2 := by
  rw [← integerNormSq_cast]
  push_cast
  rw [div_pow, div_div_eq_mul_div]

namespace RationalNormalize

/-- Numerator and denominator words emitted by integer normalization. -/
theorem integer_output_eq (y : Fin n → ℤ) (Bnum Bden m p : ℕ)
    (hupper : (m : ℚ) / 2^p = DyadicSqrt.upper
      (((integerNormSq y * Bden^2 : ℕ) : ℚ) / (Bnum : ℚ)^2) p) (i : Fin n) :
    vector (fun j => (y j : ℚ)) ((Bnum : ℚ) / (Bden : ℚ)) p i =
      (y i : ℚ) * ((Bden : ℚ) * 2^p) / ((Bnum : ℚ) * (m : ℚ)) := by
  change (((Bnum : ℚ) / (Bden : ℚ)) * DyadicSqrt.upper
    (rationalNormSq (fun j => (y j : ℚ)) / ((Bnum : ℚ) / (Bden : ℚ))^2) p)⁻¹ * (y i : ℚ) = _
  rw [integer_normalization_ratio, ← hupper]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- The output denominator is positive whenever the nonzero integer
vector lies within the stated rational norm upper bound. -/
theorem integer_output_denominator_pos (y : Fin n → ℤ) (hy : y ≠ 0)
    (Bnum Bden m p : ℕ) (hBnum : 0 < Bnum) (hBden : 0 < Bden)
    (hbound : integerNormSq y * Bden^2 ≤ Bnum^2)
    (hupper : (m : ℚ) / 2^p = DyadicSqrt.upper
      (((integerNormSq y * Bden^2 : ℕ) : ℚ) / (Bnum : ℚ)^2) p) :
    0 < Bnum * m := by
  let x : ℚ := ((integerNormSq y * Bden^2 : ℕ) : ℚ) / (Bnum : ℚ)^2
  have hx : 0 < x := by
    have hA := integerNormSq_pos y hy
    dsimp only [x]
    positivity
  have hx1 : x ≤ 1 := by
    apply (div_le_one (by positivity : 0 < (Bnum : ℚ)^2)).mpr
    exact_mod_cast hbound
  have hs := DyadicSqrt.interval_spec x hx.le hx1 p
  have hu : 0 < DyadicSqrt.upper x p := by
    change 0 < (DyadicSqrt.interval x p).2
    nlinarith [hs.1, hs.2.1, hs.2.2.2.2.1]
  have hm : 0 < m := by
    rw [← hupper] at hu
    have hmq : (0 : ℚ) < m := (div_pos_iff_of_pos_right (by positivity)).mp hu
    exact_mod_cast hmq
  exact Nat.mul_pos hBnum hm

end RationalNormalize
end Maxwell.Defect
