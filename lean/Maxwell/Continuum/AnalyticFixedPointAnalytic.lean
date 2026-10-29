import Maxwell.Continuum.AnalyticFixedPointDerivative

/-! Analytic dependence of the actual Banach fixed point. The local analytic
implicit function is identified with that constructed point using its already
proved continuity and the exact fixed-point equation. -/

noncomputable section
namespace Maxwell.Continuum.AnalyticFixedPoint.Data

open Set Metric Filter
open scoped Topology NNReal ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {F : E → ℂ → ℂ} {U : Set E} {c : ℂ} {r : ℝ} {k : ℝ≥0}
variable (D : AnalyticFixedPoint.Data F U c r k)
variable (hF : AnalyticOnNhd ℂ (Function.uncurry F) (U ×ˢ closedBall c r))
include hF

theorem analyticAt_point (p : E) (hp : p ∈ U) (hU : U ∈ 𝓝 p) :
    AnalyticAt ℂ D.point p := by
  have hparam : AnalyticAt ℂ (fun q => F q (D.point p)) p :=
    (hF (p, D.point p) ⟨hp, D.point_mem p hp⟩).comp₂ analyticAt_id analyticAt_const
  have hcont := D.continuousAt_point p hp hU hparam.continuousAt
  have hR : ContDiffAt ℂ ω (residual F) (p, D.point p) :=
    (analyticAt_residual hF p hp (D.point p) (D.point_mem p hp)).contDiffAt
  have hn : (ω : ℕ∞ω) ≠ 0 := by simp
  have hinv := D.residual_partial_invertible hF p hp (D.point p) (D.point_mem p hp)
  have hlocal : AnalyticAt ℂ (hR.implicitFunction hn hinv) p :=
    (hR.contDiffAt_implicitFunction hn hinv).analyticAt
  apply hlocal.congr
  have hgraph : Tendsto (fun q => (q, D.point q)) (𝓝 p) (𝓝 (p, D.point p)) :=
    continuousAt_id.prodMk hcont
  have hevent := hgraph.eventually (hR.eventually_apply_eq_iff_implicitFunction hn hinv)
  filter_upwards [hU, hevent] with q hq hqeq
  apply hqeq.mp
  simp only [residual, D.point_fixed q hq, D.point_fixed p hp, sub_self]

/-- Joint analyticity of the scalar map on a neighborhood of the parameter
set times the closed disk yields an analytic actual fixed point on the open
parameter set. The parameter space may be any complex Banach space. -/
theorem analyticOnNhd_point (hU : IsOpen U) : AnalyticOnNhd ℂ D.point U :=
  fun p hp => D.analyticAt_point hF p hp (hU.mem_nhds hp)

#print axioms analyticAt_point
#print axioms analyticOnNhd_point

end Maxwell.Continuum.AnalyticFixedPoint.Data
