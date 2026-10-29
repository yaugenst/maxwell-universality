import Maxwell.Continuum.WellDecayOptimization

/-! Symbolic optimization of the finite almost-analytic Taylor error.
No Taylor polynomial of enormous degree is expanded. -/

noncomputable section

namespace Maxwell.Continuum.AlmostAnalytic

def truncationOrder (t : ℝ) : ℕ := ⌊(4*t)⁻¹⌋₊

theorem remainder_geometric (K : ℕ) {t : ℝ} (ht : 0 ≤ t)
    (hK : t * (K : ℝ) ≤ 1/4) (hnext : t * ((K : ℝ)+1) ≤ 1) :
    t^(K+1) * ((K+1).factorial : ℝ)^2 / (K.factorial : ℝ) ≤ (1/2 : ℝ)^K := by
  have hfac : (K.factorial : ℝ) ≤ (K : ℝ)^K := by exact_mod_cast Nat.factorial_le_pow K
  have hcount : (K : ℝ)+1 ≤ (2 : ℝ)^K := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := K))
  have hpow : t^K * (K.factorial : ℝ) ≤ (1/4 : ℝ)^K := by
    calc
      _ ≤ t^K * (K : ℝ)^K := mul_le_mul_of_nonneg_left hfac (pow_nonneg ht K)
      _ = (t * K)^K := (mul_pow _ _ _).symm
      _ ≤ _ := pow_le_pow_left₀ (mul_nonneg ht (Nat.cast_nonneg K)) hK K
  calc
    _ = (t * ((K : ℝ)+1)) * ((K : ℝ)+1) * (t^K * (K.factorial : ℝ)) := by
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
      have hf : (K.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero K
      field_simp
    _ ≤ 1 * (2 : ℝ)^K * (1/4 : ℝ)^K := by
      apply mul_le_mul _ hpow (mul_nonneg (pow_nonneg ht K) (Nat.cast_nonneg _)) (by positivity)
      exact mul_le_mul hnext hcount (by positivity) (by norm_num)
    _ = _ := by rw [one_mul, ← mul_pow]; norm_num

theorem exp_half_le_two : Real.exp (1/2 : ℝ) ≤ 2 := by
  have he := Real.exp_lt_two_add_div_two_sub (x := (1/2 : ℝ)) (by norm_num) (by norm_num)
  norm_num at he
  linarith only [he]

theorem geometric_le_exp (K : ℕ) :
    (1/2 : ℝ)^K ≤ Real.exp (-(K : ℝ)/2) := by
  have hb : (1/2 : ℝ) ≤ Real.exp (-(1/2 : ℝ)) := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (Real.exp_pos _) exp_half_le_two
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/2) hb K
  rw [← Real.exp_nat_mul] at hp
  convert hp using 1
  congr 1
  ring

theorem truncation_remainder_exp {t : ℝ} (ht : 0 < t) (hsmall : t ≤ 1/4) :
    let K := truncationOrder t
    t^(K+1) * ((K+1).factorial : ℝ)^2 / (K.factorial : ℝ) ≤
      2 * Real.exp (-1/(8*t)) := by
  dsimp only
  let K := truncationOrder t
  have hfloor : (K : ℝ) ≤ (4*t)⁻¹ := Nat.floor_le (by positivity)
  have hfloor' : (4*t)⁻¹ - 1 < (K : ℝ) := Nat.sub_one_lt_floor _
  have hK : t * (K : ℝ) ≤ 1/4 := by
    calc
      _ ≤ t * (4*t)⁻¹ := mul_le_mul_of_nonneg_left hfloor ht.le
      _ = _ := by field_simp
  have hnext : t * ((K : ℝ)+1) ≤ 1 := by nlinarith only [hK, hsmall]
  apply ((remainder_geometric K ht.le hK hnext).trans (geometric_le_exp K)).trans
  calc
    _ ≤ Real.exp ((1/2 : ℝ)-1/(8*t)) := by
      apply Real.exp_le_exp.mpr
      have he : (4*t)⁻¹ / 2 = 1/(8*t) := by field_simp; ring
      linarith only [hfloor', he]
    _ = Real.exp (1/2 : ℝ) * Real.exp (-1/(8*t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right exp_half_le_two (Real.exp_pos _).le

end Maxwell.Continuum.AlmostAnalytic
