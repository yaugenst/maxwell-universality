import Maxwell.Continuum.PeriodicTransverseHessianBounds
import Maxwell.Continuum.PeriodicBandConjugation
import Maxwell.Continuum.PeriodicPoleReflection

/-! Reality and uniform positivity of the actual transverse Hessian at the
constructed imaginary pole. Conjugation and coordinate reflection identify
the real transverse slice before its derivatives are taken. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric Filter
open scoped Topology

attribute [local irreducible] dielectricBand hessian transverseCoefficient

theorem basisVector_star (j : Fin 3) : star (basisVector j) = basisVector j := by
  funext k
  simp only [Pi.star_apply, basisVector_apply]
  split_ifs <;> simp only [star_one, star_zero]

theorem transverseBand_imaginary_real (j k : Fin 3) (hjk : j ≠ k) (β x : ℝ)
    (hβx : |β| + |x| < analyticRadius) :
    (transverseBand j k ((β : ℂ) * Complex.I) (x : ℂ)).im = 0 := by
  let q : Momentum := ((β : ℂ) * Complex.I) • basisVector j + (x : ℂ) • basisVector k
  have hq : q ∈ physicalChart := by
    intro i
    apply (norm_le_pi_norm q i).trans_lt
    apply (two_axes_norm_le j k ((β : ℂ) * Complex.I) (x : ℂ)).trans_lt
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
      using hβx
  have he : star q = FiberReflection.momentum j q := by
    dsimp only [q]
    rw [star_add, star_smul, star_smul, basisVector_star, basisVector_star,
      reflection_add, reflection_smul, reflection_smul, reflect_basis_same,
      reflect_basis_other j k hjk]
    simp only [star_mul', Complex.star_def, Complex.conj_ofReal, Complex.conj_I,
      mul_neg, smul_neg, neg_smul]
  have hs := dielectricBand_schwarz hq
  rw [he, dielectricBand_reflect hq j] at hs
  have hi := congrArg Complex.im hs
  change (dielectricBand q).im = -(dielectricBand q).im at hi
  change (dielectricBand q).im = 0
  linarith only [hi]

theorem transverseBand_real_eventually (j k : Fin 3) (hjk : j ≠ k) {β : ℝ}
    (hβ : |β| < analyticRadius) :
    ∀ᶠ x : ℝ in 𝓝 0,
      (transverseBand j k ((β : ℂ) * Complex.I) (x : ℂ)).im = 0 := by
  filter_upwards [ball_mem_nhds (0 : ℝ) (sub_pos.mpr hβ)] with x hx
  have hx' : |x| < analyticRadius - |β| := by
    simpa only [mem_ball, Real.dist_eq, sub_zero] using hx
  exact transverseBand_imaginary_real j k hjk β x (by linarith only [hx'])

theorem transverseCoefficient_im_zero (j k : Fin 3) (hjk : j ≠ k) {β : ℝ}
    (hβ : |β| < analyticRadius) :
    (transverseCoefficient j k ((β : ℂ) * Complex.I)).im = 0 := by
  unfold transverseCoefficient
  apply RealHolomorphicCoefficients.coefficient_im_zero
    (transverseBand_analyticAt j k ?_) (transverseBand_real_eventually j k hjk hβ) 2
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
    mul_one, norm_zero, add_zero] using hβ

def transverseHessian (j k : Fin 3) (β : ℝ) : ℝ :=
  2 * (transverseCoefficient j k ((β : ℂ) * Complex.I)).re

theorem transverseHessian_derivative (j k : Fin 3) (hjk : j ≠ k) {β : ℝ}
    (hβ : |β| < analyticRadius) :
    (transverseHessian j k β : ℂ) =
      iteratedDeriv 2 (transverseBand j k ((β : ℂ) * Complex.I)) 0 := by
  have hr : ((transverseCoefficient j k ((β : ℂ) * Complex.I)).re : ℂ) =
      transverseCoefficient j k ((β : ℂ) * Complex.I) := by
    apply Complex.ext
    · simp only [Complex.ofReal_re]
    · simp only [Complex.ofReal_im, transverseCoefficient_im_zero j k hjk hβ]
  simp only [transverseHessian, Complex.ofReal_mul, Complex.ofReal_ofNat, hr]
  unfold transverseCoefficient EvenTaylor.coefficient
  norm_num
  ring

theorem transverseHessian_error (j k : Fin 3) (hjk : j ≠ k) {β : ℝ}
    (hβ0 : 0 < β) (hβ : β ≤ analyticRadius / 4) :
    |transverseHessian j k β - 2 * hessian k k| ≤
      32 * quarticConstant * β ^ 2 := by
  have hn : ‖(β : ℂ) * Complex.I‖ = β := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_I, mul_one, abs_of_pos hβ0]
  have hb := transverseCoefficient_error j k hjk (c := (β : ℂ) * Complex.I)
    (by rwa [hn]) (by rwa [hn])
  rw [hn] at hb
  have he := (Complex.abs_re_le_norm
    (transverseCoefficient j k ((β : ℂ) * Complex.I) - (hessian k k : ℂ))).trans hb
  simp only [Complex.sub_re, Complex.ofReal_re] at he
  change |2 * (transverseCoefficient j k ((β : ℂ) * Complex.I)).re - 2 * hessian k k| ≤ _
  calc
    _ = 2 * |(transverseCoefficient j k ((β : ℂ) * Complex.I)).re - hessian k k| := by
      rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ 2 * (16 * quarticConstant * β ^ 2) := mul_le_mul_of_nonneg_left he (by norm_num)
    _ = _ := by ring

theorem imaginaryPole_transverseHessian_error {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ) ^ 1024) (j k : Fin 3) (hjk : j ≠ k) :
    |transverseHessian j k (imaginaryPole D hh j) - 2 * hessian k k| ≤ 1 := by
  have hp := imaginaryPole_mem_small D hh j
  have hs := imaginary_scale_bounds D.h_pos.le hh
  have he := transverseHessian_error j k hjk (imaginaryPole_pos D hh j) (hp.2.trans hs.1)
  have hsq := pow_le_pow_left₀ hp.1 hp.2 2
  have hc := quarticConstant_nonneg
  have hm := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 32 * quarticConstant)
  calc
    _ ≤ 32 * quarticConstant * (imaginaryPole D hh j) ^ 2 := he
    _ ≤ 32 * quarticConstant * (2 * h) ^ 2 := hm
    _ ≤ 1 := by nlinarith only [hs.2.2.1]

theorem imaginaryPole_transverseHessian_bounds {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ) ^ 1024) (j k : Fin 3) (hjk : j ≠ k) :
    (2 : ℝ) ^ 98 < transverseHessian j k (imaginaryPole D hh j) ∧
      transverseHessian j k (imaginaryPole D hh j) < (2 : ℝ) ^ 110 := by
  have he := abs_le.mp (imaginaryPole_transverseHessian_error D hh j k hjk)
  have hH := hessian_diagonal_bounds k
  have hnumlo : (2 : ℝ) ^ 98 + 1 < 2 * (2 * backgroundAmplitude)⁻¹ := by
    norm_num [backgroundAmplitude]
  have hnumhi : 2 * (256 / backgroundAmplitude) + 1 < (2 : ℝ) ^ 110 := by
    norm_num [backgroundAmplitude]
  constructor <;> linarith only [he.1, he.2, hH.1, hH.2, hnumlo, hnumhi]

end Maxwell.Continuum.PeriodicBand
