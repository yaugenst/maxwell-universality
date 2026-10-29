import Maxwell.Continuum.PeriodicTransversePole

/-! A quantitative longitudinal increment estimate for the literal band
denominator. It follows from the proved operator-norm derivative variation,
uniformly on complex longitudinal segments. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric
open scoped NNReal

attribute [local irreducible] poleDenominator imaginaryPole dielectricBand poleSlope transversePole

theorem poleDenominator_increment {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum} {u : ℂ}
    (hw : ‖w‖ ≤ 1 / 4) (hu : ‖u‖ ≤ ‖w‖) :
    ‖poleDenominator D hh j (poleOffset j w u) -
      poleDenominator D hh j (poleOffset j w 0) -
      ((poleSlope D hh j : ℂ) * Complex.I) * u‖ ≤ (2 : ℝ)^123 * ‖w‖ * ‖u‖ := by
  let g : ℂ → ℂ := fun v => poleDenominator D hh j (poleOffset j w v) -
    ((poleSlope D hh j : ℂ) * Complex.I) * v
  have hd (v : ℂ) (hv : v ∈ closedBall 0 ‖w‖) :
      HasDerivAt g ((fderiv ℂ (poleDenominator D hh j) (poleOffset j w v) -
        fderiv ℂ (poleDenominator D hh j) 0) (basisVector j)) v := by
    have hk := poleOffset_norm_le (norm_nonneg w) j le_rfl
      (by simpa only [mem_closedBall, dist_zero_right] using hv)
    have ha := poleDenominator_analytic D hh j (poleOffset j w v)
      (by rw [mem_ball, dist_zero_right]; linarith only [hk, hw])
    have h1 := ha.differentiableAt.hasFDerivAt.comp_hasDerivAt v (poleOffset_hasDerivAt j w v)
    have h2 := (hasDerivAt_id v).const_mul ((poleSlope D hh j : ℂ) * Complex.I)
    have he := h1.sub h2
    rw [sub_apply, poleDenominator_basis_derivative_same]
    convert! he using 1
    simp only [mul_one]
  have hl : LipschitzOnWith ⟨(2 : ℝ)^123 * ‖w‖, by positivity⟩ g (closedBall 0 ‖w‖) := by
    apply (convex_closedBall (0 : ℂ) ‖w‖).lipschitzOnWith_of_nnnorm_deriv_le
    · intro v hv
      exact (hd v hv).differentiableAt
    · intro v hv
      rw [(hd v hv).deriv]
      have hk := poleOffset_norm_le (norm_nonneg w) j le_rfl
        (by simpa only [mem_closedBall, dist_zero_right] using hv)
      calc
        _ ≤ ‖fderiv ℂ (poleDenominator D hh j) (poleOffset j w v) -
            fderiv ℂ (poleDenominator D hh j) 0‖ * ‖basisVector j‖ :=
          (fderiv ℂ (poleDenominator D hh j) (poleOffset j w v) -
            fderiv ℂ (poleDenominator D hh j) 0).le_opNorm (basisVector j)
        _ ≤ (2 : ℝ)^123 * ‖poleOffset j w v‖ := by
          simpa only [basisVector_norm, mul_one] using poleDenominator_gradient_variation D hh j (hk.trans hw)
        _ ≤ _ := mul_le_mul_of_nonneg_left hk (by positivity)
  have he := hl.dist_le_mul u (by simpa only [mem_closedBall, dist_zero_right] using hu)
    0 (mem_closedBall_self (norm_nonneg w))
  have hg : g u - g 0 = poleDenominator D hh j (poleOffset j w u) -
      poleDenominator D hh j (poleOffset j w 0) -
      ((poleSlope D hh j : ℂ) * Complex.I) * u := by dsimp only [g]; ring
  simp only [dist_eq_norm, sub_zero, hg] at he
  convert! he using 1

theorem transversePole_norm_le_transverse {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum}
    (hw : ‖w‖ < transversePoleRadius) : ‖transversePole D hh j w‖ ≤ ‖w‖ := by
  apply (transversePole_quadratic_bound D hh j hw).trans
  have hr : (2 : ℝ)^122 * transversePoleRadius ≤ 1 := by norm_num [transversePoleRadius]
  have ha : (2 : ℝ)^122 * ‖w‖ ≤ 1 :=
    (mul_le_mul_of_nonneg_left hw.le (by positivity)).trans hr
  nlinarith only [mul_le_mul_of_nonneg_right ha (norm_nonneg w)]

theorem transversePole_increment_error {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum}
    (hw : ‖w‖ < transversePoleRadius) :
    ‖poleDenominator D hh j (poleOffset j w 0) +
      ((poleSlope D hh j : ℂ) * Complex.I) * transversePole D hh j w‖ ≤
      (2 : ℝ)^245 * ‖w‖^3 := by
  have he := poleDenominator_increment D hh j
    (hw.le.trans (pole_radii.2.2.1.trans pole_radii.2.2.2.1))
    (transversePole_norm_le_transverse D hh j hw)
  rw [transversePole_equation D hh j hw, zero_sub, sub_eq_add_neg, ← neg_add, norm_neg] at he
  calc
    _ ≤ (2 : ℝ)^123 * ‖w‖ * ‖transversePole D hh j w‖ := he
    _ ≤ (2 : ℝ)^123 * ‖w‖ * ((2 : ℝ)^122 * ‖w‖^2) :=
      mul_le_mul_of_nonneg_left (transversePole_quadratic_bound D hh j hw) (by positivity)
    _ = _ := by norm_num; ring

end Maxwell.Continuum.PeriodicBand
