import Maxwell.Continuum.NaturalSquareRootEvaluation

/-! A total executable rational square-root approximation. On a
nonnegative rational input, the proved error is the requested dyadic
precision; only integer square root and rational arithmetic are used. -/

namespace Maxwell.Continuum.Calibration

def sqrtRationalCenter (r : ℚ) (N : ℕ) : ℚ :=
  sqrtNaturalCenter (r.num.natAbs*r.den) N / r.den

theorem sqrtRationalCenter_nonneg (r : ℚ) (N : ℕ) : 0 ≤ sqrtRationalCenter r N := by
  unfold sqrtRationalCenter sqrtNaturalCenter
  positivity

theorem sqrtRational_identity {r : ℚ} (hr : 0 ≤ r) :
    Real.sqrt (r.num.natAbs*r.den : ℕ)/(r.den : ℝ) = Real.sqrt (r : ℝ) := by
  have hd : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hn : (0 : ℤ) ≤ r.num := Rat.num_nonneg.mpr hr
  have hnR : (r.num.natAbs : ℝ) = (r.num : ℝ) := by
    rw [Nat.cast_natAbs, abs_of_nonneg (by exact_mod_cast hn)]
  apply (sq_eq_sq₀ (div_nonneg (Real.sqrt_nonneg _) hd.le) (Real.sqrt_nonneg _)).mp
  rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (Rat.cast_nonneg.mpr hr)]
  rw [Nat.cast_mul, hnR, Rat.cast_def]
  field_simp

theorem sqrtRational_bracket (r : ℚ) (hr : 0 ≤ r) (N : ℕ) :
    (sqrtRationalCenter r N : ℝ) ≤ Real.sqrt (r : ℝ) ∧
      Real.sqrt (r : ℝ) < (sqrtRationalCenter r N : ℝ)+(1/2 : ℝ)^N := by
  have hd : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hd1 : (1 : ℝ) ≤ r.den := by exact_mod_cast r.den_pos
  have h := sqrtNatural_bracket (r.num.natAbs*r.den) N
  have he := sqrtRational_identity hr
  have hlo := div_le_div_of_nonneg_right h.1 hd.le
  have hhi := (div_lt_div_of_pos_right h.2 hd)
  rw [he] at hlo hhi
  have herr : (1/2 : ℝ)^N/(r.den : ℝ) ≤ (1/2 : ℝ)^N := div_le_self (by positivity) hd1
  rw [add_div] at hhi
  constructor
  · simpa only [sqrtRationalCenter, Rat.cast_div, Rat.cast_natCast] using hlo
  · have hh := hhi.trans_le (add_le_add_right herr _)
    simpa only [sqrtRationalCenter, Rat.cast_div, Rat.cast_natCast] using hh

theorem sqrtRational_error (r : ℚ) (hr : 0 ≤ r) (N : ℕ) :
    |(sqrtRationalCenter r N : ℝ)-Real.sqrt (r : ℝ)| ≤ (1/2 : ℝ)^N := by
  have h := sqrtRational_bracket r hr N
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h.1)]
  linarith only [h.2]

theorem sqrtRational_lower {r : ℚ} (hr : (4 : ℚ) ≤ r) (N : ℕ) :
    (1 : ℝ) ≤ sqrtRationalCenter r N := by
  have h4 : (4 : ℝ) ≤ r := by exact_mod_cast hr
  have hs : (2 : ℝ) ≤ Real.sqrt (r : ℝ) :=
    (Real.le_sqrt (by norm_num) (by linarith only [h4])).mpr (by norm_num; exact h4)
  have h := (sqrtRational_bracket r (by linarith only [hr]) N).2
  have he : (1/2 : ℝ)^N ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  linarith only [hs, h, he]

#print axioms sqrtRational_error
#print axioms sqrtRational_lower

end Maxwell.Continuum.Calibration
