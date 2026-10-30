import Maxwell.Continuum.PeriodicPolePlane

/-! The actual longitudinal derivative on the analytic transverse pole.
It stays quantitatively nonzero, so the selected resolvent has a literal
simple scalar denominator there. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric

attribute [local irreducible] poleDenominator imaginaryPole dielectricBand poleSlope transversePole

def poleLongitudinalDerivative {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Momentum) : ℂ :=
  fderiv ℂ (poleDenominator D hh j) k (basisVector j)

theorem poleLongitudinalDerivative_analytic {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    AnalyticOnNhd ℂ (poleLongitudinalDerivative D hh j) (ball 0 1) := by
  intro k hk
  exact ((poleDenominator_analytic D hh j k hk).fderiv.contDiffAt.clm_apply
    contDiffAt_const).analyticAt

theorem poleLongitudinalDerivative_zero {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    poleLongitudinalDerivative D hh j 0 = (poleSlope D hh j : ℂ) * Complex.I :=
  poleDenominator_basis_derivative_same D hh j

theorem poleLongitudinalDerivative_variation {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {k : Momentum} (hk : ‖k‖ ≤ 1 / 4) :
    ‖poleLongitudinalDerivative D hh j k - (poleSlope D hh j : ℂ) * Complex.I‖ ≤
      (2 : ℝ)^123 * ‖k‖ := by
  rw [← poleLongitudinalDerivative_zero D hh j]
  change ‖(fderiv ℂ (poleDenominator D hh j) k - fderiv ℂ (poleDenominator D hh j) 0) (basisVector j)‖ ≤ _
  exact ((fderiv ℂ (poleDenominator D hh j) k - fderiv ℂ (poleDenominator D hh j) 0).le_opNorm _).trans
    (by simpa only [basisVector_norm, mul_one] using poleDenominator_gradient_variation D hh j hk)

def poleCurve {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (w : Momentum) : Momentum :=
  poleOffset j w (transversePole D hh j w)

theorem poleCurve_norm {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum} (hw : ‖w‖ < transversePoleRadius) :
    ‖poleCurve D hh j w‖ ≤ ‖w‖ :=
  poleOffset_norm_le (norm_nonneg w) j le_rfl (transversePole_norm_le_transverse D hh j hw)

theorem poleCurve_zero {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) : poleCurve D hh j 0 = 0 := by
  rw [poleCurve, transversePole_zero, poleOffset_zero]

theorem poleCurve_analytic {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    AnalyticOnNhd ℂ (poleCurve D hh j) (ball 0 transversePoleRadius) := by
  intro w hw
  have hc := analyticAt_id.prod (transversePole_analytic D hh j w hw)
  convert! (poleOffset_analytic j (w, transversePole D hh j w)).comp
    (f := fun v : Momentum => (v, transversePole D hh j v)) hc using 1

theorem poleCurve_derivative_variation {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum} (hw : ‖w‖ < transversePoleRadius) :
    ‖poleLongitudinalDerivative D hh j (poleCurve D hh j w) - (poleSlope D hh j : ℂ) * Complex.I‖ ≤
      (2 : ℝ)^123 * ‖w‖ := by
  exact (poleLongitudinalDerivative_variation D hh j
    ((poleCurve_norm D hh j hw).trans
      (hw.le.trans (pole_radii.2.2.1.trans pole_radii.2.2.2.1)))).trans
    (mul_le_mul_of_nonneg_left (poleCurve_norm D hh j hw) (by positivity))

theorem poleCurve_derivative_lower {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum} (hw : ‖w‖ < transversePoleRadius) :
    1 / 2 < ‖poleLongitudinalDerivative D hh j (poleCurve D hh j w)‖ := by
  have hv := poleCurve_derivative_variation D hh j hw
  have hs : (2 : ℝ)^123 * ‖w‖ ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (hw.le.trans pole_radii.2.2.1) (by positivity)).trans pole_radii.2.2.2.2.1
  have ht := norm_sub_le ((poleSlope D hh j : ℂ) * Complex.I -
    poleLongitudinalDerivative D hh j (poleCurve D hh j w))
    (-poleLongitudinalDerivative D hh j (poleCurve D hh j w))
  rw [sub_neg_eq_add, sub_add_cancel, norm_neg, poleSlope_norm, norm_sub_rev] at ht
  linarith only [ht, hv, hs, (poleSlope_bounds D hh j).1]

theorem poleCurve_derivative_ne_zero {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum} (hw : ‖w‖ < transversePoleRadius) :
    poleLongitudinalDerivative D hh j (poleCurve D hh j w) ≠ 0 :=
  norm_pos_iff.mp (lt_trans (by norm_num) (poleCurve_derivative_lower D hh j hw))

end Maxwell.Continuum.PeriodicBand
