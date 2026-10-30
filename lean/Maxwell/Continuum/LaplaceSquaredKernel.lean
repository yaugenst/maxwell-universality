import Maxwell.Continuum.LaplaceMoment
import Mathlib.Analysis.Fourier.Inversion

/-! Integrability of the squared complex pole on the real line. This
is the absolutely integrable kernel used for Fourier inversion. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.OscillatoryPole

open Complex Real MeasureTheory Set Filter
open scoped Topology FourierTransform

def squareKernel (a : ℂ) (u : ℝ) : ℂ := 1/(a-(u : ℂ)*I)^2

theorem laplaceDenominator_ne_zero {a : ℂ} (ha : a.re < 0) (u : ℝ) : a-(u : ℂ)*I ≠ 0 := by
  intro he
  have hr := congrArg Complex.re he
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, Complex.zero_re] at hr
  exact ha.ne hr

theorem squareKernel_continuous {a : ℂ} (ha : a.re < 0) : Continuous (squareKernel a) := by
  unfold squareKernel
  exact continuous_const.div ((continuous_const.sub (Complex.continuous_ofReal.mul continuous_const)).pow 2)
    (fun u => pow_ne_zero 2 (laplaceDenominator_ne_zero ha u))

theorem squareKernel_norm {a : ℂ} (ha : a.re < 0) (u : ℝ) :
    ‖squareKernel a u‖ = (a.re^2)⁻¹*(1+(a.re⁻¹*(a.im-u))^2)⁻¹ := by
  rw [squareKernel, norm_div, norm_one, norm_pow, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, sub_zero]
  have hr : a.re ≠ 0 := ha.ne
  have hp : a.re*a.re+(a.im-u)*(a.im-u) ≠ 0 := by nlinarith only [sq_pos_of_ne_zero hr, sq_nonneg (a.im-u)]
  have hq : 1+(a.re⁻¹*(a.im-u))^2 ≠ 0 := by positivity
  field_simp
  ring

theorem squareKernel_integrable {a : ℂ} (ha : a.re < 0) : Integrable (squareKernel a) := by
  have hr := (integrable_inv_one_add_mul_sq (inv_ne_zero ha.ne)).comp_sub_left a.im
  have hn : Integrable (fun u : ℝ => ‖squareKernel a u‖) := by
    simpa only [squareKernel_norm ha] using hr.const_mul (a.re^2)⁻¹
  exact (integrable_norm_iff (squareKernel_continuous ha).aestronglyMeasurable).mp hn

#print axioms squareKernel_integrable

end Maxwell.Continuum.OscillatoryPole
