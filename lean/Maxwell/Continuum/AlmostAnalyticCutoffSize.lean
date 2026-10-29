import Maxwell.Continuum.AlmostAnalyticSupport

/-! Uniform size of the actual truncated cutoff, independent of its
symbolically enormous truncation order, and its real-axis endpoint. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.AlmostAnalytic

open Complex PeriodicBand

theorem cutoffTaylor_at_zero (K : ℕ) (q₀ : ℝ) (q β : Space) :
    cutoffTaylor K q₀ q β 0 = (Well.chi q₀ q : ℂ) := by
  unfold cutoffTaylor
  rw [Finset.sum_eq_single 0]
  · simp [coefficient, Well.directionalDerivative]
  · intro j _ hj
    simp [coefficient, hj]
  · intro h
    exact (h (Finset.mem_range.mpr (Nat.zero_lt_succ K))).elim

theorem truncated_factorial_term {t : ℝ} (ht : 0 < t) {j : ℕ}
    (hj : j ≤ truncationOrder t) : t^j * (j.factorial : ℝ) ≤ (1/2 : ℝ)^j := by
  have hfloor : (truncationOrder t : ℝ) ≤ (4*t)⁻¹ := Nat.floor_le (by positivity)
  have hj' : (j : ℝ) ≤ (truncationOrder t : ℝ) := by exact_mod_cast hj
  have htj : t*(j : ℝ) ≤ 1/2 := by
    have he : t*(4*t)⁻¹ = (1/4 : ℝ) := by field_simp
    exact ((mul_le_mul_of_nonneg_left (hj'.trans hfloor) ht.le).trans_eq he).trans (by norm_num)
  have hfac : (j.factorial : ℝ) ≤ (j : ℝ)^j := by exact_mod_cast Nat.factorial_le_pow j
  calc
    _ ≤ t^j * (j : ℝ)^j := mul_le_mul_of_nonneg_left hfac (pow_nonneg ht.le j)
    _ = (t*(j : ℝ))^j := (mul_pow _ _ _).symm
    _ ≤ _ := pow_le_pow_left₀ (by positivity) htj j

theorem cutoffTaylor_norm_le {β : Space} (hβ0 : β ≠ 0) (q : Space)
    {s : ℝ} (hs : |s| ≤ 1) :
    ‖cutoffTaylor (cutoffOrder β) smallRadius q β s‖ ≤ (2 : ℝ)^46 := by
  let t : ℝ := ((2 : ℝ)^16 / smallRadius)*‖β‖
  have ht : 0 < t := mul_pos (div_pos (by positivity) smallRadius_pos) (norm_pos_iff.mpr hβ0)
  have hterm (j : ℕ) (hj : j ∈ Finset.range (cutoffOrder β+1)) :
      ‖coefficient j s * (cutoffDerivative j β q : ℂ)‖ ≤
        (2 : ℝ)^45 * (1/2 : ℝ)^j := by
    have hcoeff : ‖coefficient j s‖ ≤ 1/(j.factorial : ℝ) := by
      rw [coefficient_norm]
      exact div_le_div_of_nonneg_right (pow_le_one₀ (abs_nonneg s) hs) (by positivity)
    have hder : ‖(cutoffDerivative j β q : ℂ)‖ ≤
        (2 : ℝ)^45 * t^j * (j.factorial : ℝ)^2 := by
      rw [norm_real, Real.norm_eq_abs]
      exact cutoff_directional_bound smallRadius smallRadius_pos q β j
    have hfac : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    rw [norm_mul]
    calc
      _ ≤ (1/(j.factorial : ℝ))*((2 : ℝ)^45*t^j*(j.factorial : ℝ)^2) :=
        mul_le_mul hcoeff hder (norm_nonneg _) (by positivity)
      _ = (2 : ℝ)^45*(t^j*(j.factorial : ℝ)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (truncated_factorial_term ht (Nat.le_of_lt_succ (Finset.mem_range.mp hj))) (by positivity)
  calc
    _ ≤ ∑ j ∈ Finset.range (cutoffOrder β+1),
        ‖coefficient j s * (cutoffDerivative j β q : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (cutoffOrder β+1), (2 : ℝ)^45*(1/2 : ℝ)^j :=
      Finset.sum_le_sum hterm
    _ = (2 : ℝ)^45 * ∑ j ∈ Finset.range (cutoffOrder β+1), (1/2 : ℝ)^j :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (2 : ℝ)^45 * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le _) (by positivity)
    _ = _ := by norm_num

#print axioms cutoffTaylor_norm_le

end Maxwell.Continuum.AlmostAnalytic
