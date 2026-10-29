import Maxwell.Continuum.AnalyticBallBounds
import Maxwell.Continuum.AnalyticLineCoefficients

/-! Explicit second- and third-order remainder estimates for actual complex
Banach-space analytic functions, obtained from their convergent line series. -/

noncomputable section

namespace Maxwell.Continuum.AnalyticBallBounds

open Set Metric

theorem scalar_tail_half {f : ℂ → ℂ} {R C : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C) (hf : AnalyticOnNhd ℂ f (ball 0 R))
    (hb : ∀ z ∈ ball 0 R, ‖f z‖ ≤ C) {z : ℂ} (hz : ‖z‖ ≤ R / 2) (n : ℕ) :
    ‖f z - ∑ k ∈ Finset.range n, EvenTaylor.coefficient f k * z ^ k‖ ≤
      (2 * C / R ^ n) * ‖z‖ ^ n := by
  have hz' : ‖z‖ < R := by linarith only [hz, hR]
  have hr0 : 0 ≤ ‖z‖ / R := div_nonneg (norm_nonneg _) hR.le
  have hr : ‖z‖ / R ≤ 1 / 2 := (div_le_iff₀ hR).mpr (by linarith only [hz])
  have hbound (k : ℕ) : ‖EvenTaylor.coefficient f k * z ^ k‖ ≤ C * (‖z‖ / R) ^ k := by
    rw [norm_mul, norm_pow]
    exact (mul_le_mul_of_nonneg_right (EvenTaylor.coefficient_norm_le hf hb hR k)
      (pow_nonneg (norm_nonneg _) k)).trans_eq (by rw [div_pow]; ring)
  have h := norm_sub_le_of_geometric_bound_of_hasSum (by linarith only [hr]) hbound
    (EvenTaylor.hasSum_coefficients hf hz') n
  rw [norm_sub_rev] at h
  apply h.trans
  calc
    C * (‖z‖ / R) ^ n / (1 - ‖z‖ / R) ≤ 2 * C * (‖z‖ / R) ^ n := by
      apply (div_le_iff₀ (by linarith only [hr] : 0 < 1 - ‖z‖ / R)).mpr
      have hp : 0 ≤ C * (‖z‖ / R) ^ n := mul_nonneg hC (pow_nonneg hr0 n)
      nlinarith only [mul_le_mul_of_nonneg_right hr hp]
    _ = _ := by rw [div_pow]; ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem line_first_coefficient {f : E → ℂ} (hf : AnalyticAt ℂ f 0) (v : E) :
    EvenTaylor.coefficient (fun z : ℂ => f (z • v)) 1 = fderiv ℂ f 0 v := by
  have hm : HasDerivAt (fun z : ℂ => z • v) v 0 := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (0 : ℂ)).smul_const v
  have hd := hf.differentiableAt.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hm (by simp)
  simp only [EvenTaylor.coefficient, Nat.factorial_one, Nat.cast_one, inv_one,
    one_mul, iteratedDeriv_one]
  exact hd.deriv

theorem line_tail_half {f : E → ℂ} {R C : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C) (hf : AnalyticOnNhd ℂ f (ball 0 R))
    (hb : ∀ x ∈ ball 0 R, ‖f x‖ ≤ C) {x : E}
    (hx0 : 0 < ‖x‖) (hx : ‖x‖ ≤ R / 2) (n : ℕ) :
    ‖f x - ∑ k ∈ Finset.range n,
        EvenTaylor.coefficient (fun z : ℂ => f (z • x)) k‖ ≤
      (2 * C / R ^ n) * ‖x‖ ^ n := by
  have hline : AnalyticOnNhd ℂ (fun z : ℂ => f (z • x)) (ball 0 (R / ‖x‖)) := by
    intro z hz
    have hz' : ‖z‖ < R / ‖x‖ := by simpa only [mem_ball, dist_zero_right] using hz
    apply AnalyticAt.comp (f := fun w : ℂ => w • x) (hf _ ?_)
      (analyticAt_id.smul analyticAt_const)
    simpa only [mem_ball, dist_zero_right, norm_smul] using (lt_div_iff₀ hx0).mp hz'
  have hbline : ∀ z ∈ ball (0 : ℂ) (R / ‖x‖), ‖f (z • x)‖ ≤ C := by
    intro z hz
    apply hb
    have hz' : ‖z‖ < R / ‖x‖ := by simpa only [mem_ball, dist_zero_right] using hz
    simpa only [mem_ball, dist_zero_right, norm_smul] using (lt_div_iff₀ hx0).mp hz'
  have h := scalar_tail_half (div_pos hR hx0) hC hline hbline (z := 1)
    (by rw [norm_one]; apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr;
        apply (le_div_iff₀ hx0).mpr; linarith only [hx]) n
  simp only [one_smul, one_pow, mul_one, norm_one] at h
  exact h.trans_eq (by rw [div_pow]; field_simp)

theorem first_remainder {f : E → ℂ} {R C : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C) (hf : AnalyticOnNhd ℂ f (ball 0 R))
    (hb : ∀ x ∈ ball 0 R, ‖f x‖ ≤ C) {x : E} (hx : ‖x‖ ≤ R / 2) :
    ‖f x - f 0 - fderiv ℂ f 0 x‖ ≤ (2 * C / R ^ 2) * ‖x‖ ^ 2 := by
  by_cases hx0 : x = 0
  · subst x
    simp only [map_zero, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero]
    rfl
  have h := line_tail_half hR hC hf hb (norm_pos_iff.mpr hx0) hx 2
  have ha := hf 0 (by simpa only [mem_ball, dist_zero_right, norm_zero] using hR)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    line_first_coefficient ha] at h
  have hzero : EvenTaylor.coefficient (fun z : ℂ => f (z • x)) 0 = f 0 := by
    simp only [EvenTaylor.coefficient, Nat.factorial_zero, Nat.cast_one, inv_one,
      iteratedDeriv_zero, zero_smul, one_mul]
  rw [hzero] at h
  simpa only [sub_add_eq_sub_sub] using h

theorem second_remainder {f : E → ℂ} {R C : ℝ}
    (hR : 0 < R) (hC : 0 ≤ C) (hf : AnalyticOnNhd ℂ f (ball 0 R))
    (hb : ∀ x ∈ ball 0 R, ‖f x‖ ≤ C) {x : E} (hx : ‖x‖ ≤ R / 2) :
    ‖f x - f 0 - fderiv ℂ f 0 x -
        EvenTaylor.coefficient (fun z : ℂ => f (z • x)) 2‖ ≤
      (2 * C / R ^ 3) * ‖x‖ ^ 3 := by
  by_cases hx0 : x = 0
  · subst x
    simp [EvenTaylor.coefficient, iteratedDeriv_const]
  have h := line_tail_half hR hC hf hb (norm_pos_iff.mpr hx0) hx 3
  have ha := hf 0 (by simpa only [mem_ball, dist_zero_right, norm_zero] using hR)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    line_first_coefficient ha] at h
  have hzero : EvenTaylor.coefficient (fun z : ℂ => f (z • x)) 0 = f 0 := by
    simp only [EvenTaylor.coefficient, Nat.factorial_zero, Nat.cast_one, inv_one,
      iteratedDeriv_zero, zero_smul, one_mul]
  rw [hzero] at h
  simpa only [sub_add_eq_sub_sub] using h

end Maxwell.Continuum.AnalyticBallBounds
