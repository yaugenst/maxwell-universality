import Maxwell.Continuum.EvenTaylor
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Analytic.ChangeOrigin

/-! Reality of holomorphic Taylor coefficients follows from reality on an
actual real neighborhood, with no conjugation-symmetry assumption. -/

noncomputable section

namespace Maxwell.Continuum.RealHolomorphicCoefficients

open Filter
open scoped Topology

theorem deriv_im_zero {f : ℂ → ℂ} {x : ℝ}
    (hf : DifferentiableAt ℂ f (x : ℂ))
    (hr : ∀ᶠ y : ℝ in 𝓝 x, (f (y : ℂ)).im = 0) :
    (deriv f (x : ℂ)).im = 0 := by
  have hd : HasDerivAt (fun y : ℝ => (f (y : ℂ)).im) (deriv f (x : ℂ)).im x :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt x hf.hasDerivAt.comp_ofReal
  have hz : HasDerivAt (fun y : ℝ => (f (y : ℂ)).im) 0 x :=
    (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hr
  exact hd.unique hz

theorem eventually_deriv_im_zero {f : ℂ → ℂ} {x : ℝ}
    (hf : AnalyticAt ℂ f (x : ℂ))
    (hr : ∀ᶠ y : ℝ in 𝓝 x, (f (y : ℂ)).im = 0) :
    ∀ᶠ y : ℝ in 𝓝 x, (deriv f (y : ℂ)).im = 0 := by
  have ha : ∀ᶠ y : ℝ in 𝓝 x, AnalyticAt ℂ f (y : ℂ) :=
    Complex.continuous_ofReal.continuousAt.eventually hf.eventually_analyticAt
  filter_upwards [ha, hr.eventually_nhds] with y hy hry
  exact deriv_im_zero hy.differentiableAt hry

theorem eventually_iteratedDeriv_im_zero {f : ℂ → ℂ} {x : ℝ}
    (hf : AnalyticAt ℂ f (x : ℂ))
    (hr : ∀ᶠ y : ℝ in 𝓝 x, (f (y : ℂ)).im = 0) (n : ℕ) :
    ∀ᶠ y : ℝ in 𝓝 x, (iteratedDeriv n f (y : ℂ)).im = 0 := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hr
  | succ n hn =>
    have hf' : AnalyticAt ℂ (iteratedDeriv n f) (x : ℂ) := by
      simpa only [iteratedDeriv_eq_iterate] using hf.iterated_deriv n
    simpa only [iteratedDeriv_succ] using
      eventually_deriv_im_zero hf' hn

theorem coefficient_im_zero {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hr : ∀ᶠ y : ℝ in 𝓝 0, (f (y : ℂ)).im = 0) (n : ℕ) :
    (EvenTaylor.coefficient f n).im = 0 := by
  have hn : (iteratedDeriv n f 0).im = 0 :=
    (eventually_iteratedDeriv_im_zero (x := 0) (by simpa using hf) hr n).self_of_nhds
  simp [EvenTaylor.coefficient, Complex.mul_im, hn]

end Maxwell.Continuum.RealHolomorphicCoefficients
