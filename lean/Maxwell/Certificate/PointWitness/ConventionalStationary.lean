import Maxwell.Certificate.PointWitness.ConventionalReflection
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.Comp

namespace Maxwell.Certificate.PointWitness

open Maxwell.Spectral Maxwell.Spectral.ConventionalAnalytic Filter
open scoped Topology
noncomputable section

/-- Evenness on physical real momenta determines the entire complex first
derivative, since that derivative is complex linear. -/
theorem conventional_point_branch_stationary
    (value : ComplexMomentum → ℂ) (hv : AnalyticAt ℂ value 0)
    (heven : ∀ᶠ q : PeriodicYee.Momentum in 𝓝 0,
      value (-realMomentum q) = value (realMomentum q)) :
    fderiv ℂ value 0 = 0 := by
  have hreal (q : PeriodicYee.Momentum) : (fderiv ℂ value 0) (realMomentum q) = 0 := by
    let f : ℝ → ℂ := fun t => value (t • realMomentum q)
    have ht : Tendsto (fun t : ℝ => t • q) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun t : ℝ => t • q) := continuous_id.smul continuous_const
      simpa only [zero_smul] using
        hc.continuousAt.tendsto (x := (0 : ℝ))
    have heq : (fun t : ℝ => f (-t)) =ᶠ[𝓝 0] f := by
      filter_upwards [ht.eventually heven] with t hh
      have hs : realMomentum (t • q) = t • realMomentum q := by
        ext j
        simp [realMomentum]
      simpa only [hs, neg_smul, f] using hh
    have hd0 : deriv f 0 = 0 := by
      have hd := heq.deriv_eq
      rw [deriv_comp_neg, neg_zero] at hd
      linear_combination -(1/2 : ℂ) * hd
    have hray : HasDerivAt (fun t : ℝ => t • realMomentum q) (realMomentum q) 0 := by
      simpa only [one_smul, id_eq] using (hasDerivAt_id (0 : ℝ)).smul_const (realMomentum q)
    have hf := (hv.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq
      0 hray (zero_smul ℝ (realMomentum q)).symm
    have he := hf.deriv
    change deriv f 0 = (fderiv ℂ value 0) (realMomentum q) at he
    exact he.symm.trans hd0
  ext z
  have hz : z = realMomentum (fun i => (z i).re) +
      Complex.I • realMomentum (fun i => (z i).im) := by
    ext i
    simp only [realMomentum, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact (Complex.re_add_im (z i)).symm.trans (by ring)
  rw [hz, map_add, map_smul, hreal, hreal, smul_zero, add_zero]
  rfl

end
end Maxwell.Certificate.PointWitness
