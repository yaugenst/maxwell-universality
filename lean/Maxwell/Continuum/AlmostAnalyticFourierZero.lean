import Maxwell.Continuum.AlmostAnalyticFourierBound

/-! The zero-shift case and a total contour estimate, including zero
spatial displacement. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.AlmostAnalytic

open Complex FreeFiber PeriodicBand Auxiliary MasterConstants MeasureTheory Set Metric

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem unshifted_fourier_bound (R : Space) (Y : Momentum → F) {M : ℝ} (hM : 0 ≤ M)
    (hY : ∀ q, ‖q‖ ≤ 4*smallRadius → ‖Y (realMomentumMap q)‖ ≤ M) :
    ‖OperatorFourier.angularFourier
        (fun q => (Well.chi smallRadius q : ℂ) • Y (realMomentumMap q)) (-R)‖ ≤ 8*M := by
  rw [OperatorFourier.angularFourier_integral]
  apply integral_norm_compact_le _ hM
  · intro q hq
    have hc : Well.chi smallRadius q ≠ 0 := by
      intro hz
      apply Function.mem_support.mp hq
      rw [hz, Complex.ofReal_zero, zero_smul, smul_zero]
    have hn := cutoff_ne_zero_norm_le hc
    have hsmall : 4*smallRadius ≤ (1 : ℝ) := by norm_num [smallRadius, backgroundAmplitude]
    simpa only [mem_closedBall, dist_zero_right] using hn.trans hsmall
  · intro q
    rw [norm_smul, OperatorFourier.angularPhase_norm, one_mul]
    by_cases hq : ‖q‖ ≤ 4*smallRadius
    · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Well.chi_nonneg smallRadius q)]
      exact (mul_le_mul (Well.chi_le_one smallRadius q) (hY q hq) (norm_nonneg _)
        (by norm_num)).trans_eq (one_mul M)
    · have hc : Well.chi smallRadius q = 0 := by
        by_contra hn
        exact hq (cutoff_ne_zero_norm_le hn)
      rw [hc, Complex.ofReal_zero, zero_smul, norm_zero]
      exact hM

theorem cutoff_fourier_bound {L : ℝ} (hL : Ls ≤ L) {β : Space}
    (hβ : ‖β‖ ≤ L⁻¹) (R : Space) (hphase : 0 ≤ inner ℝ β R)
    (Y : Momentum → F) {M M₀ : ℝ} (hM : 0 ≤ M) (hM₀ : 0 ≤ M₀)
    (hYa : ∀ s ∈ Icc (0 : ℝ) 1, ∀ q, ‖q‖ ≤ 4*smallRadius →
      AnalyticAt ℂ Y (shiftedMomentum q β s))
    (hYb : ∀ q, ‖q‖ ≤ 4*smallRadius → ‖Y (shiftedMomentum q β 1)‖ ≤ M)
    (hYs : ∀ s ∈ Icc (0 : ℝ) 1, ∀ q : Space, smallRadius ≤ ‖q‖ →
      ‖q‖ ≤ 4*smallRadius → ‖Y (shiftedMomentum q β s)‖ ≤ M₀) :
    ‖OperatorFourier.angularFourier
        (fun q => (Well.chi smallRadius q : ℂ) • Y (realMomentumMap q)) (-R)‖ ≤
      (2 : ℝ)^49 * M * Real.exp (-inner ℝ β R) +
        (2 : ℝ)^49 * M₀ * Real.exp (-cs*L) := by
  by_cases hβ0 : β = 0
  · subst β
    simp only [inner_zero_left, neg_zero, Real.exp_zero, mul_one]
    have hb : ∀ q, ‖q‖ ≤ 4*smallRadius → ‖Y (realMomentumMap q)‖ ≤ M := by
      intro q hq
      simpa only [shiftedMomentum, map_zero, smul_zero, add_zero] using hYb q hq
    exact (unshifted_fourier_bound R Y hM hb).trans
      ((mul_le_mul_of_nonneg_right (by norm_num : (8 : ℝ) ≤ 2^49) hM).trans
        (le_add_of_nonneg_right (by positivity)))
  · exact cutoff_fourier_bound_nonzero hL hβ hβ0 R hphase Y hM hM₀ hYa hYb hYs

#print axioms cutoff_fourier_bound

end Maxwell.Continuum.AlmostAnalytic
