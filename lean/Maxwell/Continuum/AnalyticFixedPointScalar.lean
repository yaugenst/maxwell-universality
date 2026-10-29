import Maxwell.Continuum.AnalyticFixedPointAnalytic
import Mathlib.Analysis.Analytic.Order

/-! Supremum perturbation bounds and simplicity of the scalar fixed-point
equation, suitable for the local spectral Schur equation. -/

noncomputable section
namespace Maxwell.Continuum.AnalyticFixedPoint.Data

open Set Metric Filter
open scoped Topology NNReal

variable {E : Type*} {F G : E → ℂ → ℂ} {U : Set E} {c : ℂ} {r : ℝ} {k k' : ℝ≥0}
variable (D : AnalyticFixedPoint.Data F U c r k)

/-- The actual supremum of the map perturbation on the closed disk controls
root displacement. Continuity supplies finiteness of that supremum. -/
theorem point_dist_point_le_sup (D' : AnalyticFixedPoint.Data G U c r k')
    (p : E) (hp : p ∈ U)
    (hF : ContinuousOn (F p) (closedBall c r))
    (hG : ContinuousOn (G p) (closedBall c r)) :
    dist (D.point p) (D'.point p) ≤
      sSup ((fun z => dist (F p z) (G p z)) '' closedBall c r) / (1 - (k : ℝ)) := by
  apply D.perturbation_bound p hp (D'.point_mem p hp) (D'.point_fixed p hp)
  have hc : ContinuousOn (fun z => dist (F p z) (G p z)) (closedBall c r) :=
    continuous_dist.comp_continuousOn (hF.prodMk hG)
  exact le_csSup ((isCompact_closedBall c r).bddAbove_image hc)
    ⟨D'.point p, D'.point_mem p hp, rfl⟩

variable [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (hF : AnalyticOnNhd ℂ (Function.uncurry F) (U ×ˢ closedBall c r))
include hF

include D in
theorem residual_deriv_ne_zero (p : E) (hp : p ∈ U) (z : ℂ)
    (hz : z ∈ closedBall c r) : deriv (fun w => w - F p w) z ≠ 0 := by
  have ha := analyticAt_slice hF p hp z hz
  have hd := (hasDerivAt_id z).sub ha.differentiableAt.hasDerivAt
  change deriv (id - F p) z ≠ 0
  rw [hd.deriv, sub_ne_zero]
  intro heq
  have hbound := D.norm_fderiv_slice_le hF p hp z hz
  rw [← norm_deriv_eq_norm_fderiv, ← heq, norm_one] at hbound
  have hk : (k : ℝ) < 1 := D.constant_lt_one
  exact (not_le_of_gt hk) hbound

/-- The scalar residual has a simple zero at the constructed root. -/
theorem residual_order_one (p : E) (hp : p ∈ U) :
    analyticOrderAt (fun z => z - F p z) (D.point p) = 1 := by
  apply (analyticAt_id.sub
    (analyticAt_slice hF p hp (D.point p) (D.point_mem p hp))).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
  · change D.point p - F p (D.point p) = 0
    rw [D.point_fixed p hp, sub_self]
  · exact D.residual_deriv_ne_zero hF p hp (D.point p) (D.point_mem p hp)

#print axioms point_dist_point_le_sup
#print axioms residual_deriv_ne_zero
#print axioms residual_order_one

end Maxwell.Continuum.AnalyticFixedPoint.Data
