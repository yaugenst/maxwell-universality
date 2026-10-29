import Maxwell.Continuum.PeriodicBandSlices

/-! Quantitative Taylor estimates for the constructed Maxwell band. The
Hessian comparison follows from the actual self-energy and a Cauchy estimate;
the fourth-order remainder follows from the proved coordinate symmetry. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber CornerBridge Metric Set

theorem slice_coefficient_sub (t : Momentum) (n : ℕ) :
    EvenTaylor.coefficient (fun z => scaledSlice t z - cornerSlice t z) n =
      EvenTaylor.coefficient (scaledSlice t) n - EvenTaylor.coefficient (cornerSlice t) n := by
  unfold EvenTaylor.coefficient
  rw [iteratedDeriv_fun_sub
    (scaledSlice_analyticAt_zero t).contDiffAt
    (cornerSlice_analyticAt_zero t).contDiffAt, mul_sub]

theorem slice_second_coefficient_comparison {t : Momentum} (ht : ∀ j, ‖t j‖ ≤ 1) :
    ‖EvenTaylor.coefficient (scaledSlice t) 2 - EvenTaylor.coefficient (cornerSlice t) 2‖ ≤
      (2 : ℝ) ^ 34 * backgroundAmplitude := by
  have hf : AnalyticOnNhd ℂ (fun z => scaledSlice t z - cornerSlice t z)
      (ball 0 (((2 : ℝ) ^ 12)⁻¹)) := by
    intro z hz
    exact (scaledSlice_analytic ht z hz).sub (cornerSlice_analytic ht z hz)
  have hC : ∀ z ∈ ball (0 : ℂ) (((2 : ℝ) ^ 12)⁻¹),
      ‖scaledSlice t z - cornerSlice t z‖ ≤ 1024 * backgroundAmplitude := by
    intro z hz
    exact scaledBand_sub_cornerBand (line_mem_chart ht (by
      simpa only [mem_ball, dist_zero_right] using hz))
  have h := EvenTaylor.coefficient_norm_le hf hC (by norm_num) 2
  rw [slice_coefficient_sub] at h
  exact h.trans_eq (by norm_num; ring)

theorem cornerSlice_second_coefficient (t : Corner.Vec) :
    EvenTaylor.coefficient (cornerSlice (realMomentum t)) 2 = (cornerQuadratic t : ℂ) := by
  simp only [EvenTaylor.coefficient, iteratedDeriv_succ', iteratedDeriv_zero,
    (cornerSlice_derivatives t).2]
  norm_num
  ring

/-- An explicit error bound for the actual directional quadratic coefficient. -/
theorem scaledSlice_quadratic_comparison (t : Corner.Vec) (ht : ∀ j, |t j| ≤ 1) :
    ‖EvenTaylor.coefficient (scaledSlice (realMomentum t)) 2 - (cornerQuadratic t : ℂ)‖ ≤
      (2 : ℝ) ^ 34 * backgroundAmplitude := by
  rw [← cornerSlice_second_coefficient]
  apply slice_second_coefficient_comparison
  intro j
  simpa only [realMomentum, Complex.norm_real, Real.norm_eq_abs] using ht j

theorem scaledSlice_quartic {t : Momentum} (ht : ∀ j, ‖t j‖ ≤ 1)
    {z : ℂ} (hz : ‖z‖ ≤ ((2 : ℝ) ^ 12)⁻¹ / 2) :
    ‖scaledSlice t z - scaledBand 0 - EvenTaylor.coefficient (scaledSlice t) 2 * z ^ 2‖ ≤
      4 * ((2 : ℝ) ^ 12) ^ 4 * ‖z‖ ^ 4 := by
  have hC : ∀ w ∈ ball (0 : ℂ) (((2 : ℝ) ^ 12)⁻¹), ‖scaledSlice t w‖ ≤ 3 * 1 := by
    intro w hw
    simpa only [scaledSlice, mul_one] using scaledBand_norm_le (line_mem_chart ht (by
      simpa only [mem_ball, dist_zero_right] using hw))
  have h := EvenTaylor.quartic_bound (scaledSlice_analytic ht) hC (by norm_num)
    (by norm_num : (0 : ℝ) ≤ 1) (scaledSlice_even t) hz
  simpa only [scaledSlice, zero_smul, mul_one, inv_inv] using h

end Maxwell.Continuum.PeriodicBand
