import Maxwell.Continuum.PeriodicGlobalNumerator
import Maxwell.Continuum.BoundedLeibniz
import Maxwell.Continuum.OperatorGevrey

/-! The actual selected source quotient has integrable order-minus-two
decay after every one of the first sixteen longitudinal derivatives,
throughout the growing chart outside the fixed pole core. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric

attribute [local irreducible] selectedPoleNumerator poleDenominator imaginaryPole

def selectedGlobalQuotient {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Momentum) : ℂ :=
  selectedPoleNumerator D hh j k / poleDenominator D hh j k

theorem selectedGlobalQuotient_line_analyticAt {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space)
    (hk : h*‖k‖ ≤ 4*smallRadius) (hk0 : poleCoreRadius ≤ ‖k‖)
    {v : Momentum} (hv : ‖v‖ ≤ 1) :
    AnalyticAt ℂ (fun ζ : ℂ => selectedGlobalQuotient D hh j (realMomentum k.ofLp + ζ • v)) 0 := by
  have hR := globalPoleRadius_pos k
  have hi := globalPole_inverse_line_analytic D hh j k hk hk0 hv 0
    (by simp only [mem_closedBall, dist_self]; positivity)
  unfold selectedGlobalQuotient
  simp only [div_eq_mul_inv]
  convert! (globalPole_source_line_analyticAt D hh j k hk v).mul hi using 1

theorem selectedGlobalQuotient_derivative {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space)
    (hk : h*‖k‖ ≤ 4*smallRadius) (hk0 : poleCoreRadius ≤ ‖k‖)
    {v : Momentum} (hv : ‖v‖ ≤ 1) {n : ℕ} (hn : n ≤ 16) :
    ‖iteratedDeriv n (fun ζ : ℂ =>
      selectedGlobalQuotient D hh j (realMomentum k.ofLp + ζ • v)) 0‖ ≤
      (2 : ℝ)^143000/(globalPoleRadius k)^2 := by
  have hR := globalPoleRadius_pos k
  have hi := globalPole_inverse_line_analytic D hh j k hk hk0 hv 0
    (by simp only [mem_closedBall, dist_self]; positivity)
  have he := BoundedLeibniz.mul_derivative_le (n := n) (x := (0 : ℂ)) (A := (2 : ℝ)^352)
    (B := (2 : ℝ)^142000/(globalPoleRadius k)^2) (by positivity)
    (globalPole_source_line_analyticAt D hh j k hk v).contDiffAt
    hi.contDiffAt
    (fun i hin => globalPole_source_derivative D hh j k hk hv (by omega : i ≤ 32))
    (fun i hin => globalPole_inverse_derivative_sixteen D hh j k hk hk0 hv (hin.trans hn))
  have he' : ‖iteratedDeriv n (fun ζ : ℂ =>
      selectedGlobalQuotient D hh j (realMomentum k.ofLp + ζ • v)) 0‖ ≤
      (2 : ℝ)^n*(2 : ℝ)^352*((2 : ℝ)^142000/(globalPoleRadius k)^2) := by
    simpa only [selectedGlobalQuotient, div_eq_mul_inv] using he
  apply he'.trans
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  rw [← pow_add, ← pow_add]
  exact pow_le_pow_right₀ (by norm_num) (by omega)

theorem selectedGlobalQuotient_real_derivative {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space)
    (hk : h*‖k‖ ≤ 4*smallRadius) (hk0 : poleCoreRadius ≤ ‖k‖)
    {v : Momentum} (hv : ‖v‖ ≤ 1) {n : ℕ} (hn : n ≤ 16) :
    ‖iteratedDeriv n (fun t : ℝ =>
      selectedGlobalQuotient D hh j (realMomentum k.ofLp + (t : ℂ) • v)) 0‖ ≤
      (2 : ℝ)^143000/(globalPoleRadius k)^2 := by
  obtain ⟨r, hr, ha⟩ := (selectedGlobalQuotient_line_analyticAt D hh j k hk hk0 hv).exists_ball_analyticOnNhd
  rw [OperatorFourier.iteratedDeriv_restrict_complex _ _ isOpen_ball ha n 0
    (by simpa only [Complex.ofReal_zero, mem_ball, dist_self] using hr)]
  exact selectedGlobalQuotient_derivative D hh j k hk hk0 hv hn

end Maxwell.Continuum.PeriodicBand
