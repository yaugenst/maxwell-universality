import Maxwell.Continuum.PeriodicImaginaryBand
import Maxwell.Continuum.AnalyticQuarticDerivative

/-! Cubic control of the derivative on imaginary momentum and strict
monotonicity of the literal band along the small positive imaginary axis. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric

attribute [local irreducible] coordinateBand dielectricBand imaginaryRise hessian

theorem imaginaryRise_hasDerivAt (j : Fin 3) {β : ℝ}
    (hβ : |β| < analyticRadius) :
    HasDerivAt (imaginaryRise j)
      (-(deriv (coordinateBand j) ((β : ℂ) * Complex.I) * Complex.I).re) β := by
  have hc := (coordinateBand_analytic j ((β : ℂ) * Complex.I) (by simpa using hβ)).differentiableAt.hasDerivAt
  have hi := hc.comp (β : ℂ) ((hasDerivAt_id (β : ℂ)).mul_const Complex.I)
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt β hi.comp_ofReal
  unfold imaginaryRise
  convert! (hasDerivAt_const β centerEnergy).sub hr using 1
  simp only [one_mul, zero_sub, Complex.reCLM_apply]

theorem imaginaryRise_derivative_error (j : Fin 3) {β : ℝ}
    (hβ0 : 0 < β) (hβ : β ≤ analyticRadius / 4) :
    |deriv (imaginaryRise j) β - 2 * hessian j j * β| ≤
      16 * quarticConstant * β^3 := by
  have hn : ‖(β : ℂ) * Complex.I‖ = β := by simp [abs_of_pos hβ0]
  have hb := AnalyticQuartic.derivative_remainder_bound
    (a := (hessian j j : ℂ)) (z := (β : ℂ) * Complex.I) (coordinateBand_analytic j)
    quarticConstant_nonneg (fun w hw => coordinateBand_quartic j hw)
    (by rwa [hn]) (by rwa [hn])
  rw [hn] at hb
  have hd := (imaginaryRise_hasDerivAt j (β := β)
    (by rw [abs_of_pos hβ0]; linarith [analyticRadius_pos])).deriv
  have he : deriv (imaginaryRise j) β - 2 * hessian j j * β =
      -((deriv (coordinateBand j) ((β : ℂ) * Complex.I) -
        2 * (hessian j j : ℂ) * ((β : ℂ) * Complex.I)) * Complex.I).re := by
    rw [hd]
    simp [Complex.mul_re, Complex.mul_im]
  rw [he, abs_neg]
  exact (Complex.abs_re_le_norm _).trans (by simpa only [norm_mul, Complex.norm_I, mul_one] using hb)

theorem imaginary_scale_bounds {h : ℝ} (h0 : 0 ≤ h)
    (hh : h ≤ 1 / (2 : ℝ)^1024) :
    2 * h ≤ analyticRadius / 4 ∧
      16 * quarticConstant * (2 * h)^2 ≤ 1 ∧
      16 * quarticConstant * h^2 ≤ 1 / 1000 ∧ h^2 ≤ 1 / 1000 := by
  have hs := pow_le_pow_left₀ h0 hh 2
  have hc := quarticConstant_nonneg
  constructor
  · exact (mul_le_mul_of_nonneg_left hh (by norm_num)).trans
      (by norm_num [analyticRadius, backgroundAmplitude])
  constructor
  · have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 64 * quarticConstant)
    have hn : 64 * quarticConstant * (1 / (2 : ℝ)^1024)^2 ≤ 1 := by
      norm_num [quarticConstant, analyticRadius, backgroundAmplitude]
    nlinarith
  constructor
  · exact (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 16 * quarticConstant)).trans
      (by norm_num [quarticConstant, analyticRadius, backgroundAmplitude])
  · exact hs.trans (by norm_num)

theorem imaginaryRise_small_error {h : ℝ} (h0 : 0 ≤ h)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {β : ℝ}
    (hβ : β ∈ Icc 0 (2 * h)) :
    |imaginaryRise j β - hessian j j * β^2| ≤ h^2 / 1000 := by
  have hb := imaginary_scale_bounds h0 hh
  have hc := quarticConstant_nonneg
  calc
    _ ≤ quarticConstant * β^4 := imaginaryRise_quartic j hβ.1 (by linarith [hβ.2])
    _ ≤ quarticConstant * (2 * h)^4 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hβ.1 hβ.2 4) hc
    _ = (16 * quarticConstant * h^2) * h^2 := by ring
    _ ≤ (1 / 1000 : ℝ) * h^2 :=
      mul_le_mul_of_nonneg_right hb.2.2.1 (sq_nonneg h)
    _ = _ := by ring

theorem imaginaryRise_deriv_pos {h : ℝ} (h0 : 0 < h)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {β : ℝ}
    (hβ : β ∈ Ioo 0 (2 * h)) : 0 < deriv (imaginaryRise j) β := by
  have hb := imaginary_scale_bounds h0.le hh
  have he := (abs_le.mp (imaginaryRise_derivative_error j hβ.1 (hβ.2.le.trans hb.1))).1
  have hs : β^2 ≤ (2 * h)^2 := pow_le_pow_left₀ hβ.1.le hβ.2.le 2
  have hC := quarticConstant_nonneg
  have hc : 16 * quarticConstant * β^2 ≤ 1 :=
    (mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 16 * quarticConstant)).trans hb.2.1
  have hm := mul_le_mul_of_nonneg_right hc hβ.1.le
  have hH := mul_le_mul_of_nonneg_right (hessian_diagonal_ge_one j) hβ.1.le
  nlinarith [hβ.1]

theorem imaginaryRise_strictMonoOn {h : ℝ} (h0 : 0 < h)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    StrictMonoOn (imaginaryRise j) (Icc 0 (2 * h)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 (2 * h))
  · intro β hβ
    apply (imaginaryRise_hasDerivAt j ?_).continuousAt.continuousWithinAt
    rw [abs_of_nonneg hβ.1]
    exact hβ.2.trans_lt (lt_of_le_of_lt (imaginary_scale_bounds h0.le hh).1
      (by linarith [analyticRadius_pos]))
  · intro β hβ
    rw [interior_Icc] at hβ
    exact imaginaryRise_deriv_pos h0 hh j hβ

end Maxwell.Continuum.PeriodicBand
