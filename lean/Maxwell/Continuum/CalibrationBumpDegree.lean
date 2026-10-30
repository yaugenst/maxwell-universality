import Maxwell.Continuum.CalibrationBumpGuard

/-! A concrete rationally computed Fourier degree. Its logarithmic
rounding guards are paid for by the fixed master constant, leaving a
degree quadratic in precision and linear in the torus scale. -/

namespace Maxwell.Continuum.Calibration

open MasterConstants

def rootDegreeValue (s : ℚ) (N ell : ℕ) : ℚ :=
  (2 : ℚ)^(3*exponent)*s*((N+ell+2 : ℕ) : ℚ)^2

def rootDegree (s : ℚ) (N ell : ℕ) : ℕ := ⌈rootDegreeValue s N ell⌉₊

theorem rootDegreeValue_real (s : ℚ) (N ell : ℕ) :
    (rootDegreeValue s N ell : ℝ) = Cs^3*(s : ℝ)*((N+ell+2 : ℕ) : ℝ)^2 := by
  unfold rootDegreeValue Cs
  push_cast
  rw [← pow_mul]
  congr 2

theorem rootDegree_lower (s : ℚ) (N ell : ℕ) :
    Cs^3*(s : ℝ)*((N+ell+2 : ℕ) : ℝ)^2 ≤ (rootDegree s N ell : ℝ) := by
  have h : (rootDegreeValue s N ell : ℝ) ≤ ((⌈rootDegreeValue s N ell⌉₊ : ℚ) : ℝ) :=
    Rat.cast_le.mpr (Nat.le_ceil (rootDegreeValue s N ell))
  simpa only [rootDegree, rootDegreeValue_real, Rat.cast_natCast] using h

theorem rootDegreeValue_one (s : ℚ) (hs : 4 ≤ (s : ℝ)) (N ell : ℕ) :
    (1 : ℝ) ≤ (rootDegreeValue s N ell : ℝ) := by
  rw [rootDegreeValue_real]
  have hc : (1 : ℝ) ≤ Cs^3 := one_le_pow₀ Cs_ge_one
  have hx : (1 : ℝ) ≤ ((N+ell+2 : ℕ) : ℝ)^2 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ N+ell+2 by omega))
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hc (by linarith)) hx

theorem rootDegree_pos (s : ℚ) (hs : 4 ≤ (s : ℝ)) (N ell : ℕ) : 0 < rootDegree s N ell := by
  have h := rootDegreeValue_one s hs N ell
  rw [rootDegreeValue_real] at h
  have hl := rootDegree_lower s N ell
  exact_mod_cast (show (0 : ℝ) < (rootDegree s N ell : ℝ) by linarith)

theorem rootDegree_upper (s : ℚ) (hs : 4 ≤ (s : ℝ)) (N ell : ℕ) :
    (rootDegree s N ell : ℝ) ≤ 2*Cs^3*(s : ℝ)*((N+ell+2 : ℕ) : ℝ)^2 := by
  have hpos : 0 ≤ rootDegreeValue s N ell := Rat.cast_nonneg.mp ((rootDegreeValue_one s hs N ell).trans' zero_le_one)
  have hc : ((⌈rootDegreeValue s N ell⌉₊ : ℚ) : ℝ) < ((rootDegreeValue s N ell+1 : ℚ) : ℝ) :=
    Rat.cast_lt.mpr (Nat.ceil_lt_add_one hpos)
  simp only [Rat.cast_add, Rat.cast_natCast, Rat.cast_one] at hc
  change (rootDegree s N ell : ℝ) < (rootDegreeValue s N ell : ℝ)+1 at hc
  have ho := rootDegreeValue_one s hs N ell
  rw [rootDegreeValue_real] at hc ho
  nlinarith

theorem nat_cast_le_two_pow (n : ℕ) : (n : ℝ) ≤ (2 : ℝ)^n :=
  (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans (by
    have hn (k : ℕ) : (k : ℝ)+1 ≤ (2 : ℝ)^k := by
      induction k with
      | zero => norm_num
      | succ k ih => rw [Nat.cast_succ, pow_succ]; nlinarith [Nat.cast_nonneg (α := ℝ) k]
    exact hn n)

theorem rootDegree_pow_bound (s : ℚ) (hs : 4 ≤ (s : ℝ)) (N ell : ℕ)
    (hlog : (s : ℝ) ≤ (2 : ℝ)^ell) :
    (rootDegree s N ell : ℝ) ≤ (2 : ℝ)^(1+3*exponent+ell+2*(N+ell+2)) := by
  have hCs0 := Cs_pos
  calc
    _ ≤ 2*Cs^3*(s : ℝ)*((N+ell+2 : ℕ) : ℝ)^2 := rootDegree_upper s hs N ell
    _ ≤ 2*Cs^3*((2 : ℝ)^ell)*((2 : ℝ)^(N+ell+2))^2 := by
      gcongr
      exact nat_cast_le_two_pow _
    _ = _ := by
      rw [Cs, ← pow_mul, ← pow_mul]
      nth_rw 1 [show (2 : ℝ) = 2^1 from (pow_one _).symm]
      rw [← pow_add, ← pow_add, ← pow_add]
      congr 1
      omega

theorem rootDegree_guard_bound (s : ℚ) (hs : 4 ≤ (s : ℝ)) (N ell : ℕ)
    (hlog : (s : ℝ) ≤ (2 : ℝ)^ell) :
    rootCoefficientGuard (rootDegree s N ell) ≤ 9*exponent+9*ell+6*N+21 := by
  have hq := rootDegree_pow_bound s hs N ell hlog
  have hq1 : (1 : ℝ) ≤ rootDegree s N ell := by exact_mod_cast rootDegree_pos s hs N ell
  have hh : ((2*rootDegree s N ell+1 : ℕ) : ℝ) ≤
      (2 : ℝ)^(3+3*exponent+ell+2*(N+ell+2)) := by
    calc
      _ ≤ 4*(rootDegree s N ell : ℝ) := by push_cast; linarith
      _ ≤ 4*(2 : ℝ)^(1+3*exponent+ell+2*(N+ell+2)) := mul_le_mul_of_nonneg_left hq (by norm_num)
      _ = _ := by
        rw [show (4 : ℝ) = 2^2 by norm_num, ← pow_add]
        congr 1
        omega
  have hn : 2*rootDegree s N ell+1 ≤ 2^(3+3*exponent+ell+2*(N+ell+2)) := by exact_mod_cast hh
  have hc := Nat.clog_le_of_le_pow hn
  unfold rootCoefficientGuard
  omega

theorem rootDegree_admissible (s : ℚ) (hs : 4 ≤ (s : ℝ)) (N ell : ℕ)
    (hlog : (s : ℝ) ≤ (2 : ℝ)^ell) :
    Cs^2*(s : ℝ)*((N+rootCoefficientGuard (rootDegree s N ell) : ℕ)+(ell : ℝ)+2)^2 ≤
      (rootDegree s N ell : ℝ) := by
  have hg := rootDegree_guard_bound s hs N ell hlog
  have hgr : (rootCoefficientGuard (rootDegree s N ell) : ℝ) ≤
      9*(exponent : ℝ)+9*(ell : ℝ)+6*(N : ℝ)+21 := by exact_mod_cast hg
  have hp : (9*(exponent : ℝ)+23)^2 ≤ Cs := by
    have hnum : (9*(exponent : ℝ)+23)^2 ≤ (2 : ℝ)^88 := by norm_num [exponent]
    exact hnum.trans (fixed_power_le_Cs (by have := exponent_large; omega))
  have he : (10 : ℝ) ≤ 9*(exponent : ℝ)+23 := by linarith [Nat.cast_nonneg (α := ℝ) exponent]
  have hN := mul_le_mul_of_nonneg_right (show (7 : ℝ) ≤ 9*(exponent : ℝ)+23 by linarith)
    (Nat.cast_nonneg (α := ℝ) N)
  have hell := mul_le_mul_of_nonneg_right he (Nat.cast_nonneg (α := ℝ) ell)
  have ht : ((N+rootCoefficientGuard (rootDegree s N ell) : ℕ) : ℝ)+(ell : ℝ)+2 ≤
      (9*(exponent : ℝ)+23)*((N+ell+2 : ℕ) : ℝ) := by push_cast; nlinarith
  calc
    _ ≤ Cs^2*(s : ℝ)*((9*(exponent : ℝ)+23)*((N+ell+2 : ℕ) : ℝ))^2 := by gcongr
    _ = Cs^2*(s : ℝ)*((9*(exponent : ℝ)+23)^2*((N+ell+2 : ℕ) : ℝ)^2) := by ring
    _ ≤ Cs^2*(s : ℝ)*(Cs*((N+ell+2 : ℕ) : ℝ)^2) := by gcongr
    _ = Cs^3*(s : ℝ)*((N+ell+2 : ℕ) : ℝ)^2 := by ring
    _ ≤ _ := rootDegree_lower s N ell

#print axioms rootDegree_admissible

end Maxwell.Continuum.Calibration
