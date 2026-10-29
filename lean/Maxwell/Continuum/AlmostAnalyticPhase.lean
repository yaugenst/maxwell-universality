import Maxwell.Continuum.AlmostAnalyticContourBound
import Maxwell.Continuum.AlmostAnalyticCutoffSize
import Maxwell.Continuum.OperatorFourierIntegral

/-! Holomorphic Fourier phase and its exact decay along the literal
almost-analytic contour. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.AlmostAnalytic

open Complex FreeFiber PeriodicBand Auxiliary MeasureTheory Set Metric

def complexPhase (R : Space) (q : Momentum) : ℂ :=
  Complex.exp (I * ∑ j : Fin 3, q j * (R j : ℂ))

theorem complexPhase_analytic (R : Space) (q : Momentum) :
    AnalyticAt ℂ (complexPhase R) q := by
  apply AnalyticAt.cexp
  apply analyticAt_const.mul
  exact Finset.analyticAt_fun_sum _ (fun j _ =>
    ((ContinuousLinearMap.proj j : Momentum →L[ℂ] ℂ).analyticAt q).mul analyticAt_const)

theorem complexPhase_shifted_norm (R q β : Space) (s : ℝ) :
    ‖complexPhase R (shiftedMomentum q β s)‖ = Real.exp (-s*inner ℝ β R) := by
  rw [complexPhase, Complex.norm_exp]
  congr 1
  simp only [shiftedMomentum, realMomentumMap, ContinuousLinearMap.pi_apply,
    ContinuousLinearMap.comp_apply, PiLp.proj_apply, Complex.ofRealCLM_apply,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, star_trivial, Fin.sum_univ_three, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem complexPhase_real (R q : Space) :
    complexPhase R (realMomentumMap q) = OperatorFourier.angularPhase q (-R) := by
  unfold complexPhase OperatorFourier.angularPhase
  congr 1
  simp only [realMomentumMap, ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
    PiLp.proj_apply, Complex.ofRealCLM_apply, inner_neg_right, neg_neg,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial,
    Fin.sum_univ_three, Complex.ofReal_add, Complex.ofReal_mul]
  ring

theorem shiftedMomentum_at_zero (q β : Space) :
    shiftedMomentum q β 0 = realMomentumMap q := by
  simp only [shiftedMomentum, Complex.ofReal_zero, mul_zero, zero_smul, add_zero]

theorem contourProduct_at_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (K : ℕ) (β : Space) (Y : Momentum → F) (q : Space) :
    contourProduct K β Y 0 q = (Well.chi smallRadius q : ℂ) • Y (realMomentumMap q) := by
  rw [contourProduct, cutoffTaylor_at_zero, shiftedMomentum_at_zero]

#print axioms complexPhase_shifted_norm

end Maxwell.Continuum.AlmostAnalytic
