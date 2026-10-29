import Maxwell.Continuum.AnalyticFixedPointScalar
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! Extracting the first two derivatives from an actual local quadratic
identity with analytic coefficient. -/

noncomputable section
namespace Maxwell.Continuum.RankOneBand

open Filter
open scoped Topology

theorem quadratic_derivatives {f b : ℂ → ℂ} {c a : ℂ}
    (hb : AnalyticAt ℂ b 0)
    (hf : f =ᶠ[𝓝 0] fun z => c + a * z + z ^ 2 * b z) :
    deriv f 0 = a ∧ deriv (deriv f) 0 = 2 * b 0 := by
  have hfirst : HasDerivAt (fun z => c + a * z + z ^ 2 * b z) a 0 := by
    convert ((hasDerivAt_const 0 c).add ((hasDerivAt_id 0).const_mul a)).add
      (((hasDerivAt_id 0).pow 2).mul hb.differentiableAt.hasDerivAt) using 1
    · rfl
    · simp
  have heq : deriv (fun z => c + a * z + z ^ 2 * b z) =ᶠ[𝓝 0]
      fun z => a + 2 * z * b z + z ^ 2 * deriv b z := by
    filter_upwards [hb.eventually_analyticAt] with z hz
    have h := ((hasDerivAt_const z c).add ((hasDerivAt_id z).const_mul a)).add
      (((hasDerivAt_id z).pow 2).mul hz.differentiableAt.hasDerivAt)
    convert h.deriv using 1
    · rfl
    · simp only [Nat.cast_ofNat, id_eq, Pi.pow_apply]
      ring
  have hsecond : HasDerivAt (fun z => a + 2 * z * b z + z ^ 2 * deriv b z)
      (2 * b 0) 0 := by
    convert ((hasDerivAt_const 0 a).add
      (((hasDerivAt_id 0).const_mul 2).mul hb.differentiableAt.hasDerivAt)).add
        (((hasDerivAt_id 0).pow 2).mul hb.deriv.differentiableAt.hasDerivAt) using 1
    · rfl
    · simp
  exact ⟨hf.deriv_eq.trans hfirst.deriv,
    (hf.deriv.trans heq).deriv_eq.trans hsecond.deriv⟩

#print axioms quadratic_derivatives

end Maxwell.Continuum.RankOneBand
