import Maxwell.Continuum.PeriodicPoleNumerator
import Maxwell.Continuum.PeriodicPoleResidueDerivative

/-! The literal source residue on the actual analytic pole. Its uniform
variation estimate uses the full normalized source and the actual
longitudinal derivative; neither quantity is supplied as free data. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric

attribute [local irreducible] poleDenominator imaginaryPole dielectricBand poleSlope
  transversePole poleCurve selectedPoleNumerator poleLongitudinalDerivative

theorem residue_division_variation {N N₀ a b : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (ha : 1 ≤ ‖a‖) (hb : 1 / 2 ≤ ‖b‖) (hN₀ : ‖N₀‖ ≤ (2 : ℝ)^64)
    (hN : ‖N - N₀‖ ≤ (2 : ℝ)^66 * r) (hB : ‖b - a‖ ≤ (2 : ℝ)^123 * r) :
    ‖N / b - N₀ / a‖ ≤ (2 : ℝ)^192 * r := by
  have ha0 : a ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) ha)
  have hb0 : b ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (by norm_num) hb)
  have he : N / b - N₀ / a = (N - N₀) / b + N₀ * (a - b) / (b * a) := by
    field_simp [ha0, hb0]
    ring
  have hbpos : 0 < ‖b‖ := lt_of_lt_of_le (by norm_num) hb
  have hden : 1 / 2 ≤ ‖b * a‖ := by
    rw [norm_mul]
    calc
      _ = (1 / 2 : ℝ) * 1 := by ring
      _ ≤ _ := mul_le_mul hb ha (by norm_num) (norm_nonneg b)
  have h1 : ‖(N - N₀) / b‖ ≤ (2 : ℝ)^67 * r := by
    rw [norm_div]
    apply (div_le_iff₀ hbpos).mpr
    have hm := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ (2 : ℝ)^67 * r)
    have hc : (2 : ℝ)^67 / 2 = (2 : ℝ)^66 := by norm_num
    nlinarith only [hN, hm, hc]
  have h2 : ‖N₀ * (a - b) / (b * a)‖ ≤ (2 : ℝ)^188 * r := by
    rw [norm_div]
    apply (div_le_iff₀ (lt_of_lt_of_le (by norm_num) hden)).mpr
    have hn : ‖N₀ * (a - b)‖ ≤ (2 : ℝ)^187 * r := by
      rw [norm_mul, norm_sub_rev]
      have hm := mul_le_mul hN₀ hB (norm_nonneg _) (by positivity : (0 : ℝ) ≤ 2^64)
      exact hm.trans_eq (by norm_num; ring)
    have hm := mul_le_mul_of_nonneg_left hden (by positivity : 0 ≤ (2 : ℝ)^188 * r)
    have hc : (2 : ℝ)^188 / 2 = (2 : ℝ)^187 := by norm_num
    nlinarith only [hn, hm, hc]
  rw [he]
  exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans (by
    have hc : (2 : ℝ)^67 + (2 : ℝ)^188 ≤ (2 : ℝ)^192 := by norm_num
    simpa only [add_mul] using mul_le_mul_of_nonneg_right hc hr))

def selectedPoleAmplitude {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (w : Momentum) : ℂ :=
  selectedPoleNumerator D hh j (poleCurve D hh j w) /
    poleLongitudinalDerivative D hh j (poleCurve D hh j w)

theorem selectedPoleAmplitude_zero {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    selectedPoleAmplitude D hh j 0 =
      selectedPoleNumerator D hh j 0 / ((poleSlope D hh j : ℂ) * Complex.I) := by
  rw [selectedPoleAmplitude, poleCurve_zero, poleLongitudinalDerivative_zero]

theorem selectedPoleAmplitude_zero_bound {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    ‖selectedPoleAmplitude D hh j 0‖ ≤ (2 : ℝ)^64 := by
  rw [selectedPoleAmplitude_zero, norm_div, poleSlope_norm]
  exact (div_le_self (norm_nonneg _) (poleSlope_bounds D hh j).1.le).trans
    (selectedPoleNumerator_bound D hh j (by simp))

theorem selectedPoleAmplitude_variation {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum} (hw : ‖w‖ < transversePoleRadius) :
    ‖selectedPoleAmplitude D hh j w - selectedPoleAmplitude D hh j 0‖ ≤
      (2 : ℝ)^192 * ‖w‖ := by
  have hk : ‖poleCurve D hh j w‖ ≤ 1 / 8 :=
    (poleCurve_norm D hh j hw).trans
      (hw.le.trans (by norm_num [transversePoleRadius]))
  have hn := (selectedPoleNumerator_variation D hh j hk).trans
    (mul_le_mul_of_nonneg_left (poleCurve_norm D hh j hw) (by positivity))
  rw [selectedPoleAmplitude_zero, selectedPoleAmplitude]
  apply residue_division_variation (norm_nonneg w)
    (by rw [poleSlope_norm]; exact (poleSlope_bounds D hh j).1.le)
    (poleCurve_derivative_lower D hh j hw).le
    (selectedPoleNumerator_bound D hh j (by simp)) hn
    (poleCurve_derivative_variation D hh j hw)

theorem selectedPoleAmplitude_continuousOn {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    ContinuousOn (selectedPoleAmplitude D hh j) (ball 0 transversePoleRadius) := by
  have hc := (poleCurve_analytic D hh j).continuousOn
  have hm : MapsTo (poleCurve D hh j) (ball 0 transversePoleRadius) (closedBall 0 (1 / 8)) := by
    intro w hw
    rw [mem_closedBall, dist_zero_right]
    exact (poleCurve_norm D hh j (by simpa only [mem_ball, dist_zero_right] using hw)).trans
      ((le_of_lt (by simpa only [mem_ball, dist_zero_right] using hw)).trans
        (by norm_num [transversePoleRadius]))
  have hn := (selectedPoleNumerator_lipschitz D hh j).continuousOn.comp hc hm
  have hd := (poleLongitudinalDerivative_analytic D hh j).continuousOn.comp hc
    (fun w hw => by
      have he := hm hw
      rw [mem_closedBall, dist_zero_right] at he
      rw [mem_ball, dist_zero_right]
      linarith only [he])
  apply hn.div hd
  intro w hw
  exact poleCurve_derivative_ne_zero D hh j (by simpa only [mem_ball, dist_zero_right] using hw)

end Maxwell.Continuum.PeriodicBand
