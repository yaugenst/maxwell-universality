import Maxwell.Continuum.PeriodicPoleDivision
import Mathlib.Analysis.Complex.Schwarz

/-! Quantitative bounds on the actual analytic division. The pole divisor
is bounded away from zero by the same proved contraction, and the regular
part is bounded using Schwarz's estimate for its divided difference. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric
open scoped NNReal

attribute [local irreducible] poleDenominator imaginaryPole dielectricBand poleSlope
  selectedPoleNumerator selectedPoleAmplitude selectedPoleDivisor selectedRegularFactor

theorem selectedPoleDivisor_lower {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum} (hw : ‖w‖ < transversePoleRadius)
    {u : ℂ} (hu : ‖u‖ ≤ longitudinalPoleRadius) :
    1 / 2 ≤ ‖selectedPoleDivisor D hh j w u‖ := by
  by_cases he : u = transversePole D hh j w
  · subst u
    rw [selectedPoleDivisor_at_pole D hh j hw]
    exact (poleCurve_derivative_lower D hh j hw).le
  have hr := (poleContractionData D hh j).residual_bound w
    (by simpa only [mem_ball, dist_zero_right] using hw)
    (z := u) (by simpa only [mem_closedBall, dist_zero_right] using hu)
  change dist u (transversePole D hh j w) ≤ dist u (poleMap D hh j w u) / (1 - ((1 / 2 : ℝ≥0) : ℝ)) at hr
  simp only [dist_eq_norm, poleMap, sub_sub_cancel, norm_div, poleSlope_norm,
    NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] at hr
  rw [← selectedPoleDivisor_factor D hh j hw u, norm_mul] at hr
  have hc : 0 < poleSlope D hh j := lt_trans (by norm_num) (poleSlope_bounds D hh j).1
  have h1 := (le_div_iff₀ (by norm_num : (0 : ℝ) < 1 - 1 / 2)).mp hr
  have h2 := (le_div_iff₀ hc).mp h1
  have hn : 0 < ‖u - transversePole D hh j w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
  nlinarith only [h2, hn, (poleSlope_bounds D hh j).1]

theorem selectedRegularFactor_bound {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum} (hw : ‖w‖ < transversePoleRadius)
    {u : ℂ} (hu : ‖u‖ ≤ longitudinalPoleRadius) :
    ‖selectedRegularFactor D hh j w u‖ ≤ (2 : ℝ)^65 := by
  have hd := selectedPoleDivisor_lower D hh j hw hu
  have hk := poleOffset_norm_le pole_radii.1.le j (hw.le.trans pole_radii.2.2.1) hu
  have hn := selectedPoleNumerator_bound D hh j
    (hk.trans (pole_radii.2.2.2.1.trans (by norm_num)))
  rw [selectedRegularFactor, norm_div]
  apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hd)).mpr
  have hm := mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ 2^65)
  have hc : (2 : ℝ)^65 * (1 / 2) = (2 : ℝ)^64 := by norm_num
  linarith only [hn, hm, hc]

theorem transversePole_small_disk {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum} (hw : ‖w‖ < transversePoleRadius) :
    ‖transversePole D hh j w‖ ≤ longitudinalPoleRadius / 8 := by
  apply (transversePole_quadratic_bound D hh j hw).trans
  apply (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg w) hw.le 2) (by positivity)).trans
  norm_num [transversePoleRadius, longitudinalPoleRadius]

theorem selectedRegularPart_bound {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum} (hw : ‖w‖ < transversePoleRadius)
    {u : ℂ} (hu : ‖u‖ ≤ longitudinalPoleRadius / 4) :
    ‖selectedRegularPart D hh j w u‖ ≤ (2 : ℝ)^1091 := by
  have hp := transversePole_small_disk D hh j hw
  have hmap {v : ℂ} (hv : v ∈ ball (transversePole D hh j w) (longitudinalPoleRadius / 2)) :
      ‖v‖ ≤ longitudinalPoleRadius := by
    have hv' : ‖v - transversePole D hh j w‖ < longitudinalPoleRadius / 2 := by
      simpa only [mem_ball, dist_eq_norm] using hv
    have hn := norm_add_le (v - transversePole D hh j w) (transversePole D hh j w)
    rw [sub_add_cancel] at hn
    linarith only [hn, hv', hp, pole_radii.1]
  have hd : DifferentiableOn ℂ (selectedRegularFactor D hh j w)
      (ball (transversePole D hh j w) (longitudinalPoleRadius / 2)) :=
    fun v hv => (selectedRegularFactor_analytic D hh j hw (hmap hv)).differentiableAt.differentiableWithinAt
  have hmaps : MapsTo (selectedRegularFactor D hh j w)
      (ball (transversePole D hh j w) (longitudinalPoleRadius / 2))
      (closedBall (selectedRegularFactor D hh j w (transversePole D hh j w)) ((2 : ℝ)^66)) := by
    intro v hv
    rw [mem_closedBall, dist_eq_norm]
    exact (norm_sub_le _ _).trans ((add_le_add
      (selectedRegularFactor_bound D hh j hw (hmap hv))
      (selectedRegularFactor_bound D hh j hw (transversePole_norm D hh j hw))).trans_eq (by norm_num))
  have humem : u ∈ ball (transversePole D hh j w) (longitudinalPoleRadius / 2) := by
    rw [mem_ball, dist_eq_norm]
    exact (norm_sub_le _ _).trans_lt (by linarith only [hu, hp, pole_radii.1])
  have he := Complex.norm_dslope_le_div_of_mapsTo_ball hd hmaps humem
  change ‖selectedRegularPart D hh j w u‖ ≤ _ at he
  exact he.trans_eq (by norm_num [longitudinalPoleRadius])

#print axioms selectedRegularPart_bound

end Maxwell.Continuum.PeriodicBand
