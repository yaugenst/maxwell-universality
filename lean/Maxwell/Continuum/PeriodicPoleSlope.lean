import Maxwell.Continuum.PeriodicPoleDerivative

/-! The quantitative scaled longitudinal derivative at the actual pole,
with the constants used by the transverse implicit-function argument. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary

attribute [local irreducible] coordinateBand imaginaryPole hessian imaginaryRise

theorem imaginaryPole_derivative_error_small {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    |(deriv (coordinateBand j) ((imaginaryPole D hh j : ℂ) * Complex.I)).im -
      2 * hessian j j * imaginaryPole D hh j| ≤ imaginaryPole D hh j := by
  have hp := imaginaryPole_mem_small D hh j
  have hb := imaginary_scale_bounds D.h_pos.le hh
  have hc := quarticConstant_nonneg
  have hs := pow_le_pow_left₀ hp.1 hp.2 2
  have hcoef : 16 * quarticConstant * (imaginaryPole D hh j)^2 ≤ 1 :=
    (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 16 * quarticConstant)).trans hb.2.1
  have hval : 16 * quarticConstant * (imaginaryPole D hh j)^3 ≤ imaginaryPole D hh j := by
    nlinarith [mul_le_mul_of_nonneg_right hcoef hp.1]
  have he := (imaginaryRise_derivative_error j (imaginaryPole_pos D hh j)
    (hp.2.trans hb.1)).trans hval
  rw [imaginaryRise_derivative_eq j (by
    rw [abs_of_pos (imaginaryPole_pos D hh j)]
    exact hp.2.trans_lt (lt_of_le_of_lt hb.1 (by linarith [analyticRadius_pos])))] at he
  exact he

theorem sqrt_hessian_diagonal_upper (j : Fin 3) : Real.sqrt (hessian j j) ≤ (2 : ℝ)^54 := by
  have hH : hessian j j ≤ ((2 : ℝ)^54)^2 :=
    (hessian_diagonal_bounds j).2.trans (by norm_num [backgroundAmplitude])
  have hs := Real.sqrt_le_sqrt hH
  rwa [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 2^54)] at hs

theorem pole_slope_arithmetic {h H s β d : ℝ} (h0 : 0 < h) (hH : 1 ≤ H)
    (hs : 2 ≤ s) (hsu : s ≤ (2 : ℝ)^54) (hsq : s^2 = H)
    (hβ0 : 0 ≤ β) (hβh : β ≤ h)
    (hlo : (99 / 100 : ℝ) * h ≤ β * s)
    (hhi : β * s ≤ (101 / 100 : ℝ) * h)
    (he : |d - 2 * H * β| ≤ β) : 1 < d / h ∧ d / h < (2 : ℝ)^112 := by
  have hs0 : 0 ≤ s := by linarith
  have heq : β * s * s = H * β := by rw [← hsq]; ring
  have hlo' := mul_le_mul_of_nonneg_right hlo hs0
  have hhi' := mul_le_mul_of_nonneg_right hhi hs0
  rw [heq] at hlo' hhi'
  have htwo := mul_le_mul_of_nonneg_right hs h0.le
  have hone := mul_le_mul_of_nonneg_right hH hβ0
  have he' := abs_le.mp he
  constructor
  · apply (lt_div_iff₀ h0).mpr
    nlinarith
  · have hu := mul_le_mul_of_nonneg_left hsu (by positivity : 0 ≤ (101 / 100 : ℝ) * h)
    have hd : d ≤ (2 * (101 / 100 : ℝ) * 2^54 + 1) * h := by nlinarith
    apply (div_lt_iff₀ h0).mpr
    exact hd.trans_lt (mul_lt_mul_of_pos_right (by norm_num) h0)

def poleSlope {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) : ℝ :=
  (deriv (coordinateBand j) ((imaginaryPole D hh j : ℂ) * Complex.I)).im / h

theorem poleSlope_bounds {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    1 < poleSlope D hh j ∧ poleSlope D hh j < (2 : ℝ)^112 := by
  have hsp := Real.sqrt_pos.mpr (hessian_diagonal_positive j)
  have hp := imaginaryPole_bounds D hh j
  have hlo := (div_le_iff₀ hsp).mp hp.1
  have hhi := (le_div_iff₀ hsp).mp hp.2
  exact pole_slope_arithmetic D.h_pos (hessian_diagonal_ge_one j)
    (sqrt_hessian_diagonal_ge_two j) (sqrt_hessian_diagonal_upper j)
    (Real.sq_sqrt (hessian_diagonal_positive j).le)
    (imaginaryPole_pos D hh j).le (imaginaryPole_le_inverse_scale D hh j)
    hlo hhi (imaginaryPole_derivative_error_small D hh j)

end Maxwell.Continuum.PeriodicBand
