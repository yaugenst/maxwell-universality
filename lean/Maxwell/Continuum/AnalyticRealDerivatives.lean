import Maxwell.Continuum.OscillatoryDerivatives
import Mathlib.Analysis.Complex.RealDeriv

/-! The real derivatives of a holomorphic function on the real axis
are its literal complex derivatives. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum

open Complex Filter
open scoped Topology ContDiff

theorem analyticAt_iteratedDeriv_ofReal {f : ℂ → ℂ} {u : ℝ}
    (hf : AnalyticAt ℂ f (u : ℂ)) (n : ℕ) :
    iteratedDeriv n (fun x : ℝ => f (x : ℂ)) u = iteratedDeriv n f (u : ℂ) := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih =>
    have he : iteratedDeriv n (fun x : ℝ => f (x : ℂ)) =ᶠ[𝓝 u]
        fun x : ℝ => iteratedDeriv n f (x : ℂ) := by
      filter_upwards [Complex.continuous_ofReal.continuousAt.eventually hf.eventually_analyticAt] with x hx
      exact ih hx
    rw [iteratedDeriv_succ, he.deriv_eq]
    have ha : AnalyticAt ℂ (iteratedDeriv n f) (u : ℂ) := by
      simpa only [iteratedDeriv_eq_iterate] using hf.iterated_deriv n
    rw [ha.differentiableAt.hasDerivAt.comp_ofReal.deriv, iteratedDeriv_succ]

#print axioms analyticAt_iteratedDeriv_ofReal

end Maxwell.Continuum
