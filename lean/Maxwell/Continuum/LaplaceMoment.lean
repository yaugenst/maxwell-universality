import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The first complex Laplace moment on the half-line, proved from
actual integrability and the fundamental theorem of calculus. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.OscillatoryPole

open Complex Real MeasureTheory Set Filter
open scoped Topology

theorem integrableOn_linear_exp {a : ℂ} (ha : a.re < 0) :
    IntegrableOn (fun t : ℝ => (t : ℂ)*Complex.exp (a*t)) (Ioi 0) := by
  have hr : IntegrableOn (fun t : ℝ => t*Real.exp (a.re*t)) (Ioi 0) := by
    simpa only [Real.rpow_one, neg_neg] using
      (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := 1) (b := -a.re)
        (by norm_num) (by norm_num) (by linarith only [ha]))
  have hn : IntegrableOn (fun t : ℝ => ‖(t : ℂ)*Complex.exp (a*t)‖) (Ioi 0) := by
    apply hr.congr_fun _ measurableSet_Ioi
    intro t ht
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (show 0 < t from ht),
      Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact (integrable_norm_iff (by apply Continuous.aestronglyMeasurable; fun_prop)).mp hn

theorem tendsto_linear_exp_zero {a : ℂ} (ha : a.re < 0) :
    Tendsto (fun t : ℝ => (t : ℂ)*Complex.exp (a*t)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hr : Tendsto (fun t : ℝ => t*Real.exp (a.re*t)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one, neg_neg] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (-a.re) (by linarith only [ha])
  apply hr.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht,
    Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

theorem integral_linear_exp {a : ℂ} (ha : a.re < 0) :
    (∫ t : ℝ in Ioi 0, (t : ℂ)*Complex.exp (a*t)) = 1/a^2 := by
  have ha0 : a ≠ 0 := by intro hz; simp only [hz, Complex.zero_re, lt_self_iff_false] at ha
  let P : ℝ → ℂ := fun t => ((t : ℂ)/a - 1/a^2)*Complex.exp (a*t)
  have hd (t : ℝ) : HasDerivAt P ((t : ℂ)*Complex.exp (a*t)) t := by
    have ht : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
    have he := ((ht.div_const a).sub_const (1/a^2)).mul ((ht.const_mul a).cexp)
    convert he using 1
    field_simp
    ring
  have hExp : Tendsto (fun t : ℝ => Complex.exp (a*t)) atTop (𝓝 0) := by
    simpa only [Complex.tendsto_exp_nhds_zero_iff, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero, id_eq] using
      tendsto_const_nhds.neg_mul_atTop ha tendsto_id
  have hp : Tendsto P atTop (𝓝 0) := by
    have he := ((tendsto_linear_exp_zero ha).div_const a).sub (hExp.const_mul (1/a^2))
    simpa only [zero_div, mul_zero, sub_zero] using he.congr (fun t => by dsimp only [P]; ring)
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ => hd t)
    (integrableOn_linear_exp ha) hp
  simpa only [P, Complex.ofReal_zero, zero_div, zero_sub, mul_zero, Complex.exp_zero,
    mul_one, neg_neg] using hi

#print axioms integral_linear_exp

end Maxwell.Continuum.OscillatoryPole
