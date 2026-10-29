import Maxwell.Continuum.PeriodicPoleQuadratic
import Maxwell.Continuum.PeriodicPoleIncrement

/-! The cubic transverse pole estimate for the actual Maxwell band. The
quadratic form is the literal band Hessian at the imaginary pole. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric

attribute [local irreducible] poleDenominator imaginaryPole dielectricBand poleSlope
  transversePole transverseCoefficient poleQuadratic

theorem poleTransverseDenominator_cubic {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum} (hw : ‖w‖ ≤ 1 / 2) :
    ‖poleDenominator D hh j (poleOffset j w 0) - poleQuadratic D hh j w‖ ≤
      (2 : ℝ)^121 * ‖w‖^3 := by
  have hb := AnalyticBallBounds.second_remainder
    (R := 1) (C := (2 : ℝ)^120) (by norm_num) (by positivity)
    (poleDenominator_analytic D hh j)
    (fun x hx => poleDenominator_bound D hh j
      (le_of_lt (by simpa only [mem_ball, dist_zero_right] using hx)))
    ((poleOffset_zero_norm_le j w).trans hw)
  have he : (fun ζ : ℂ => poleDenominator D hh j (ζ • poleOffset j w 0)) =
      fun ζ => poleTransverseDenominator D hh j (ζ • w) := by
    funext ζ
    simp only [poleTransverseDenominator, poleOffset_smul]
  rw [poleDenominator_zero, poleDenominator_fderiv_zero, poleOffset_same, mul_zero,
    sub_zero, sub_zero, he, poleTransverseDenominator_second] at hb
  have hc : 2 * (2 : ℝ)^120 = (2 : ℝ)^121 := by norm_num
  simp only [one_pow, div_one, hc] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (poleOffset_zero_norm_le j w) 3) (by positivity))

def poleQuadraticPhase {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (w : Momentum) : ℂ :=
  -(poleQuadratic D hh j w) / ((poleSlope D hh j : ℂ) * Complex.I)

theorem transversePole_cubic {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum}
    (hw : ‖w‖ < transversePoleRadius) :
    ‖transversePole D hh j w - poleQuadraticPhase D hh j w‖ ≤
      (2 : ℝ)^246 * ‖w‖^3 := by
  have hb := poleTransverseDenominator_cubic D hh j
    (hw.le.trans (pole_radii.2.2.1.trans (pole_radii.2.2.2.1.trans (by norm_num))))
  have hi := transversePole_increment_error D hh j hw
  have he : transversePole D hh j w - poleQuadraticPhase D hh j w =
      (poleQuadratic D hh j w + ((poleSlope D hh j : ℂ) * Complex.I) *
        transversePole D hh j w) / ((poleSlope D hh j : ℂ) * Complex.I) := by
    unfold poleQuadraticPhase
    rw [add_div, mul_div_cancel_left₀ _ (poleSlope_ne_zero D hh j), neg_div, sub_neg_eq_add]
    ring
  have ht := norm_add_le (poleQuadratic D hh j w - poleDenominator D hh j (poleOffset j w 0))
    (poleDenominator D hh j (poleOffset j w 0) +
      ((poleSlope D hh j : ℂ) * Complex.I) * transversePole D hh j w)
  have hid : poleQuadratic D hh j w - poleDenominator D hh j (poleOffset j w 0) +
      (poleDenominator D hh j (poleOffset j w 0) +
        ((poleSlope D hh j : ℂ) * Complex.I) * transversePole D hh j w) =
      poleQuadratic D hh j w + ((poleSlope D hh j : ℂ) * Complex.I) * transversePole D hh j w := by ring
  rw [hid, norm_sub_rev] at ht
  rw [he, norm_div, poleSlope_norm]
  calc
    _ ≤ ‖poleQuadratic D hh j w + ((poleSlope D hh j : ℂ) * Complex.I) *
        transversePole D hh j w‖ := div_le_self (norm_nonneg _) (poleSlope_bounds D hh j).1.le
    _ ≤ (2 : ℝ)^121 * ‖w‖^3 + (2 : ℝ)^245 * ‖w‖^3 := ht.trans (add_le_add hb hi)
    _ ≤ _ := by
      have hc : (2 : ℝ)^121 + (2 : ℝ)^245 ≤ (2 : ℝ)^246 := by norm_num
      simpa only [add_mul] using mul_le_mul_of_nonneg_right hc (pow_nonneg (norm_nonneg w) 3)

end Maxwell.Continuum.PeriodicBand
