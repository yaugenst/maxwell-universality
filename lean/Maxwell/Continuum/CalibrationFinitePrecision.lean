import Maxwell.Continuum.CalibrationFiniteAlgorithm

/-! Symbolic dyadic budgets for the literal finite calibration program.
No large power is evaluated in establishing these inequalities. -/

namespace Maxwell.Continuum.Calibration

private theorem half_power_monotone (a b : ℕ) (h : a≤b) :
    (1/2 : ℝ)^b ≤ (1/2 : ℝ)^a :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) h

theorem dyadic_normalize_small (d W : ℕ) (h : d+3≤W) :
    (1/2 : ℝ)^W ≤ (1/2 : ℝ)^d/8 := by
  apply (half_power_monotone (d+3) W h).trans_eq
  rw [pow_add]
  ring

theorem dyadic_normalize_error (N d W : ℕ) (h : N+d+4≤W) :
    10*(1/2 : ℝ)^W/(1/2 : ℝ)^d ≤ (1/2 : ℝ)^N := by
  have hd : 0 < (1/2 : ℝ)^d := by positivity
  apply (div_le_iff₀ hd).mpr
  calc
    _ ≤ 10*(1/2 : ℝ)^(N+d+4) :=
      mul_le_mul_of_nonneg_left (half_power_monotone _ _ h) (by norm_num)
    _ = ((1/2 : ℝ)^N*(1/2 : ℝ)^d)*(10*(1/2 : ℝ)^4) := by
      rw [pow_add (1/2 : ℝ) (N+d) 4,pow_add (1/2 : ℝ) N d]
      ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) (by norm_num)

namespace FiniteAlgorithm

attribute [local irreducible] workPrecision rootBits size

private theorem seed_guard (n ell k : ℕ) :
    n+(39+2*k)+4 ≤ n+2*ell+4*k+256 := by omega

private theorem seed_small_guard (n ell k : ℕ) :
    (39+2*k)+3 ≤ n+2*ell+4*k+256 := by omega

theorem seed_normalize_small (L r N : ℕ) :
    (1/2 : ℝ)^precision L r N ≤ (1/2 : ℝ)^(39+2*rootBits L r N)/8 :=
  dyadic_normalize_small _ _ (seed_small_guard (workPrecision N) (lengthBits L) (rootBits L r N))

theorem seed_normalize_budget (L r N : ℕ) :
    10*(1/2 : ℝ)^precision L r N/(1/2 : ℝ)^(39+2*rootBits L r N) ≤
      (1/2 : ℝ)^workPrecision N :=
  dyadic_normalize_error _ _ _ (seed_guard (workPrecision N) (lengthBits L) (rootBits L r N))

#print axioms seed_normalize_budget

end FiniteAlgorithm
end Maxwell.Continuum.Calibration
