import Maxwell.Continuum.PeriodicImaginaryDerivative

/-! Strict monotonicity on the fixed physical small chart, so the
constructed pole is unique throughout that chart, not only its enclosure. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Set

attribute [local irreducible] imaginaryRise hessian

theorem smallRadius_le_quarter : smallRadius ≤ analyticRadius / 4 := by
  norm_num [smallRadius, analyticRadius, backgroundAmplitude]

theorem small_chart_derivative_error_factor :
    16 * quarticConstant * smallRadius^2 ≤ (2 * backgroundAmplitude)⁻¹ := by
  norm_num [quarticConstant, smallRadius, analyticRadius, backgroundAmplitude]

theorem imaginaryRise_deriv_pos_chart (j : Fin 3) {β : ℝ}
    (hβ : β ∈ Ioo 0 smallRadius) : 0 < deriv (imaginaryRise j) β := by
  have he := (abs_le.mp
    (imaginaryRise_derivative_error j hβ.1 (hβ.2.le.trans smallRadius_le_quarter))).1
  have hs : β^2 ≤ smallRadius^2 := pow_le_pow_left₀ hβ.1.le hβ.2.le 2
  have hc := quarticConstant_nonneg
  have hb : 16 * quarticConstant * β^2 ≤ hessian j j :=
    ((mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 16 * quarticConstant)).trans
      small_chart_derivative_error_factor).trans (hessian_diagonal_bounds j).1
  have hm := mul_le_mul_of_nonneg_right hb hβ.1.le
  have hp := mul_pos (hessian_diagonal_positive j) hβ.1
  nlinarith

theorem imaginaryRise_strictMonoOn_chart (j : Fin 3) :
    StrictMonoOn (imaginaryRise j) (Icc 0 smallRadius) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 smallRadius)
  · intro β hβ
    apply (imaginaryRise_hasDerivAt j ?_).continuousAt.continuousWithinAt
    rw [abs_of_nonneg hβ.1]
    exact hβ.2.trans_lt (lt_of_le_of_lt smallRadius_le_quarter
      (by linarith [analyticRadius_pos]))
  · intro β hβ
    rw [interior_Icc] at hβ
    exact imaginaryRise_deriv_pos_chart j hβ

theorem twice_inverse_scale_le_smallRadius {h : ℝ} (hh : h ≤ 1 / (2 : ℝ)^1024) :
    2 * h ≤ smallRadius :=
  (mul_le_mul_of_nonneg_left hh (by norm_num)).trans
    (by norm_num [smallRadius, backgroundAmplitude])

end Maxwell.Continuum.PeriodicBand
