import Maxwell.Continuum.AnalyticFixedPointContinuity
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-! The contraction controls the complex derivative even on the disk boundary.
The residual `z - F(p,z)` therefore has invertible scalar partial derivative. -/

noncomputable section
namespace Maxwell.Continuum.AnalyticFixedPoint

open Set Metric Filter
open scoped Topology NNReal ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {F : E → ℂ → ℂ} {U : Set E} {c : ℂ} {r : ℝ} {k : ℝ≥0}

def residual (F : E → ℂ → ℂ) (v : E × ℂ) : ℂ := v.2 - F v.1 v.2

namespace Data

variable (D : AnalyticFixedPoint.Data F U c r k)
variable (hF : AnalyticOnNhd ℂ (Function.uncurry F) (U ×ˢ closedBall c r))
include hF

theorem analyticAt_slice (p : E) (hp : p ∈ U) (z : ℂ) (hz : z ∈ closedBall c r) :
    AnalyticAt ℂ (F p) z :=
  (hF (p, z) ⟨hp, hz⟩).comp₂ analyticAt_const analyticAt_id

include D in
/-- The interior estimate extends to the boundary by continuity of the
analytic derivative. Thus a fixed point on the boundary causes no gap. -/
theorem norm_fderiv_slice_le (p : E) (hp : p ∈ U) (z : ℂ) (hz : z ∈ closedBall c r) :
    ‖fderiv ℂ (F p) z‖ ≤ (k : ℝ) := by
  have hclosure : closure (ball c r) = closedBall c r := closure_ball c D.radius_pos.ne'
  apply le_on_closure (s := ball c r) (f := fun w => ‖fderiv ℂ (F p) w‖)
    (g := fun _ => (k : ℝ)) ?_ ?_ continuousOn_const (by rwa [hclosure])
  · intro w hw
    exact norm_fderiv_le_of_lipschitzOn ℂ
      (mem_of_superset (isOpen_ball.mem_nhds hw) ball_subset_closedBall) (D.lipschitz p hp)
  · rw [hclosure]
    intro w hw
    have hc : ContDiffAt ℂ ω (F p) w := (analyticAt_slice hF p hp w hw).contDiffAt
    exact (hc.continuousAt_fderiv (by simp)).norm.continuousWithinAt

theorem analyticAt_residual (p : E) (hp : p ∈ U) (z : ℂ) (hz : z ∈ closedBall c r) :
    AnalyticAt ℂ (residual F) (p, z) :=
  analyticAt_snd.sub (hF (p, z) ⟨hp, hz⟩)

theorem residual_partial_eq (p : E) (hp : p ∈ U) (z : ℂ) (hz : z ∈ closedBall c r) :
    (fderiv ℂ (residual F) (p, z)).comp (ContinuousLinearMap.inr ℂ E ℂ) =
      1 - fderiv ℂ (F p) z := by
  have hwhole := (analyticAt_residual hF p hp z hz).differentiableAt.hasFDerivAt
  have hcomp := hwhole.comp z (hasFDerivAt_prodMk_right p z)
  have hslice := (hasFDerivAt_id z).sub
    (analyticAt_slice hF p hp z hz).differentiableAt.hasFDerivAt
  exact hcomp.unique hslice

include D in
theorem residual_partial_invertible (p : E) (hp : p ∈ U) (z : ℂ)
    (hz : z ∈ closedBall c r) :
    ((fderiv ℂ (residual F) (p, z)).comp (ContinuousLinearMap.inr ℂ E ℂ)).IsInvertible := by
  rw [residual_partial_eq hF p hp z hz]
  have hk : (k : ℝ) < 1 := D.constant_lt_one
  obtain ⟨u, hu⟩ := isUnit_one_sub_of_norm_lt_one
    ((D.norm_fderiv_slice_le hF p hp z hz).trans_lt hk)
  refine ⟨ContinuousLinearEquiv.unitsEquiv ℂ ℂ u, ?_⟩
  exact hu

#print axioms norm_fderiv_slice_le
#print axioms residual_partial_invertible

end Data
end Maxwell.Continuum.AnalyticFixedPoint
