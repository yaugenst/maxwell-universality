import Maxwell.Continuum.RankOneBandFamily

/-! Analytic dependence and simplicity of the constructed rank-one band,
including an analytic nonzero vector in the literal operator kernel. -/

noncomputable section
namespace Maxwell.Continuum.RankOneBand.Data

set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped NNReal Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {K : H →L[ℂ] H} {u : H} {ell : ℝ}
variable (D : Data K u ell) {V : E → ℂ → H →L[ℂ] H} {U : Set E}
variable (P : PerturbationData V U ell)
variable (hV : AnalyticOnNhd ℂ (Function.uncurry V) (U ×ˢ closedBall (ell : ℂ) (1 / 100)))
include hV

omit [CompleteSpace E] in
include D P hV in
theorem analyticOnNhd_scalarMap : AnalyticOnNhd ℂ (Function.uncurry (scalarMap K u ell V))
    (U ×ˢ closedBall (ell : ℂ) (1 / 100)) := by
  intro p hp
  exact D.analyticAt_rootMap (Function.uncurry V) Prod.snd p (hV p hp) analyticAt_snd
    (P.small p.1 hp.1 p.2 hp.2) (by simpa only [mem_closedBall, dist_eq_norm] using hp.2)

theorem analyticOnNhd_bandRoot (hU : IsOpen U) : AnalyticOnNhd ℂ (D.bandRoot P) U :=
  (D.contractionData P).analyticOnNhd_point (D.analyticOnNhd_scalarMap P hV) hU

theorem analyticOnNhd_bandVector (hU : IsOpen U) : AnalyticOnNhd ℂ (D.bandVector P) U := by
  intro p hp
  have hr := D.analyticOnNhd_bandRoot P hV hU p hp
  have hm := D.bandRoot_mem P p hp
  have hcomp : AnalyticAt ℂ (fun q => V q (D.bandRoot P q)) p :=
    (hV (p, D.bandRoot P p) ⟨hp, hm⟩).comp₂ analyticAt_id hr
  exact D.analyticAt_eigenvectorLift (fun q => V q (D.bandRoot P q)) (D.bandRoot P) p
    hcomp hr (P.small p hp _ hm) (by simpa only [mem_closedBall, dist_eq_norm] using hm)

omit [CompleteSpace E] in
theorem scalar_residual_order_one (p : E) (hp : p ∈ U) :
    analyticOrderAt (fun e => e - scalarMap K u ell V p e) (D.bandRoot P p) = 1 :=
  (D.contractionData P).residual_order_one (D.analyticOnNhd_scalarMap P hV) p hp

#print axioms analyticOnNhd_bandRoot
#print axioms analyticOnNhd_bandVector
#print axioms scalar_residual_order_one

end Maxwell.Continuum.RankOneBand.Data
