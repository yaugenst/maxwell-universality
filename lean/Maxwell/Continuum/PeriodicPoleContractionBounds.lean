import Maxwell.Continuum.PeriodicPoleCoordinates

/-! Uniform contraction estimates for the actual selected-band transverse
pole. The scalar derivative is compared with the literal longitudinal
derivative, using operator-norm Cauchy bounds on the rescaled denominator. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric
open scoped NNReal

attribute [local irreducible] poleDenominator imaginaryPole dielectricBand poleSlope

def longitudinalPoleRadius : ℝ := (2 ^ 1024 : ℝ)⁻¹
def transversePoleRadius : ℝ := (2 ^ 2048 : ℝ)⁻¹

theorem pole_radii : 0 < longitudinalPoleRadius ∧ 0 < transversePoleRadius ∧
    transversePoleRadius ≤ longitudinalPoleRadius ∧ longitudinalPoleRadius ≤ 1 / 4 ∧
    (2 : ℝ)^123 * longitudinalPoleRadius ≤ 1 / 2 ∧
    (2 : ℝ)^121 * transversePoleRadius ^ 2 ≤ longitudinalPoleRadius / 2 := by
  norm_num [longitudinalPoleRadius, transversePoleRadius]

def poleMap {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1 / (2 : ℝ)^1024)
    (j : Fin 3) (w : Momentum) (u : ℂ) : ℂ :=
  u - poleDenominator D hh j (poleOffset j w u) / ((poleSlope D hh j : ℂ) * Complex.I)

theorem poleSlope_norm {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1 / (2 : ℝ)^1024)
    (j : Fin 3) : ‖(poleSlope D hh j : ℂ) * Complex.I‖ = poleSlope D hh j := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (lt_trans (by norm_num) (poleSlope_bounds D hh j).1), Complex.norm_I, mul_one]

theorem poleSlope_ne_zero {h z : ℝ} (D : Calibration h z) (hh : h ≤ 1 / (2 : ℝ)^1024)
    (j : Fin 3) : (poleSlope D hh j : ℂ) * Complex.I ≠ 0 :=
  norm_pos_iff.mp (by rw [poleSlope_norm]; linarith only [(poleSlope_bounds D hh j).1])

theorem poleDenominator_gradient_variation {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {k : Momentum} (hk : ‖k‖ ≤ 1 / 4) :
    ‖fderiv ℂ (poleDenominator D hh j) k - fderiv ℂ (poleDenominator D hh j) 0‖ ≤
      (2 : ℝ)^123 * ‖k‖ := by
  have hb := AnalyticBallBounds.fderiv_sub_bound
    (R := 1) (C := (2 : ℝ)^120) (by norm_num) (by positivity)
    (poleDenominator_analytic D hh j)
    (fun x hx => poleDenominator_bound D hh j
      (le_of_lt (by simpa only [mem_ball, dist_zero_right] using hx))) hk
    (y := 0) (by simp)
  have hc : 8 * (2 : ℝ)^120 = (2 : ℝ)^123 := by norm_num
  simpa only [one_pow, div_one, sub_zero, hc] using hb

theorem poleMap_hasDerivAt {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (w : Momentum) {u : ℂ}
    (hu : ‖poleOffset j w u‖ ≤ 1 / 4) :
    HasDerivAt (poleMap D hh j w)
      (1 - (fderiv ℂ (poleDenominator D hh j) (poleOffset j w u) (basisVector j)) /
        ((poleSlope D hh j : ℂ) * Complex.I)) u := by
  have ha := poleDenominator_analytic D hh j (poleOffset j w u)
    (by rw [mem_ball, dist_zero_right]; linarith only [hu])
  have hd := ha.differentiableAt.hasFDerivAt.comp_hasDerivAt u (poleOffset_hasDerivAt j w u)
  have h := (hasDerivAt_id u).sub (hd.div_const ((poleSlope D hh j : ℂ) * Complex.I))
  convert! h using 1

theorem poleMap_derivative_bound {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum} {u : ℂ}
    (hu : ‖poleOffset j w u‖ ≤ longitudinalPoleRadius) :
    ‖deriv (poleMap D hh j w) u‖ ≤ 1 / 2 := by
  have hk := hu.trans pole_radii.2.2.2.1
  rw [(poleMap_hasDerivAt D hh j w hk).deriv]
  have he : 1 - fderiv ℂ (poleDenominator D hh j) (poleOffset j w u) (basisVector j) /
      ((poleSlope D hh j : ℂ) * Complex.I) =
      -((fderiv ℂ (poleDenominator D hh j) (poleOffset j w u) -
        fderiv ℂ (poleDenominator D hh j) 0) (basisVector j)) /
          ((poleSlope D hh j : ℂ) * Complex.I) := by
    rw [sub_apply, poleDenominator_basis_derivative_same]
    have hc : (poleSlope D hh j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (lt_trans (by norm_num : (0 : ℝ) < 1) (poleSlope_bounds D hh j).1).ne'
    field_simp [hc]
    ring
  rw [he, norm_div, norm_neg, poleSlope_norm]
  have hnum : ‖(fderiv ℂ (poleDenominator D hh j) (poleOffset j w u) -
      fderiv ℂ (poleDenominator D hh j) 0) (basisVector j)‖ ≤
      (2 : ℝ)^123 * ‖poleOffset j w u‖ := by
    exact ((fderiv ℂ (poleDenominator D hh j) (poleOffset j w u) -
      fderiv ℂ (poleDenominator D hh j) 0).le_opNorm (basisVector j)).trans
        (by simpa only [basisVector_norm, mul_one] using poleDenominator_gradient_variation D hh j hk)
  calc
    _ ≤ ‖(fderiv ℂ (poleDenominator D hh j) (poleOffset j w u) -
          fderiv ℂ (poleDenominator D hh j) 0) (basisVector j)‖ :=
      div_le_self (norm_nonneg _) (poleSlope_bounds D hh j).1.le
    _ ≤ (2 : ℝ)^123 * ‖poleOffset j w u‖ := hnum
    _ ≤ (2 : ℝ)^123 * longitudinalPoleRadius := mul_le_mul_of_nonneg_left hu (by positivity)
    _ ≤ 1 / 2 := pole_radii.2.2.2.2.1

theorem poleMap_lipschitz {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum}
    (hw : ‖w‖ ≤ transversePoleRadius) :
    LipschitzOnWith (1 / 2 : ℝ≥0) (poleMap D hh j w) (closedBall 0 longitudinalPoleRadius) := by
  apply (convex_closedBall (0 : ℂ) longitudinalPoleRadius).lipschitzOnWith_of_nnnorm_deriv_le
  · intro u hu
    apply (poleMap_hasDerivAt D hh j w ?_).differentiableAt
    exact (poleOffset_norm_le pole_radii.1.le j (hw.trans pole_radii.2.2.1)
      (by simpa only [mem_closedBall, dist_zero_right] using hu)).trans pole_radii.2.2.2.1
  · intro u hu
    exact poleMap_derivative_bound D hh j
      (poleOffset_norm_le pole_radii.1.le j (hw.trans pole_radii.2.2.1)
        (by simpa only [mem_closedBall, dist_zero_right] using hu))

theorem poleMap_zero_bound {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {w : Momentum} (hw : ‖w‖ ≤ 1 / 2) :
    ‖poleMap D hh j w 0‖ ≤ (2 : ℝ)^121 * ‖w‖^2 := by
  have hk := (poleOffset_zero_norm_le j w).trans hw
  have hb := AnalyticBallBounds.first_remainder
    (R := 1) (C := (2 : ℝ)^120) (by norm_num) (by positivity)
    (poleDenominator_analytic D hh j)
    (fun x hx => poleDenominator_bound D hh j
      (le_of_lt (by simpa only [mem_ball, dist_zero_right] using hx))) hk
  rw [poleDenominator_zero, poleDenominator_fderiv_zero, poleOffset_same, mul_zero,
    sub_zero, sub_zero] at hb
  have hc : 2 * (2 : ℝ)^120 = (2 : ℝ)^121 := by norm_num
  simp only [one_pow, div_one, hc] at hb
  rw [poleMap, zero_sub, norm_neg, norm_div, poleSlope_norm]
  exact (div_le_self (norm_nonneg _) (poleSlope_bounds D hh j).1.le).trans
    (hb.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (poleOffset_zero_norm_le j w) 2) (by positivity)))

end Maxwell.Continuum.PeriodicBand
