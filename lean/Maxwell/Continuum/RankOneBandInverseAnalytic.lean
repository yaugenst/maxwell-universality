import Maxwell.Continuum.RankOneBandInverseBounds
import Maxwell.Continuum.RankOneBandFamilyAnalytic

/-! Analyticity of every literal factor in the rank-one Schur inverse. -/

noncomputable section
namespace Maxwell.Continuum.RankOneBand.Data

set_option backward.isDefEq.respectTransparency false

open scoped ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {K : H →L[ℂ] H} {u : H} {ell : ℝ} (D : Data K u ell)

include D in
theorem analyticAt_highSolve (V : X → H →L[ℂ] H) (e : X → ℂ) (x : X)
    (hV : AnalyticAt ℂ V x) (he : AnalyticAt ℂ e x)
    (hs : ‖V x‖ ≤ 1 / 256) (hd : ‖e x - (ell : ℂ)‖ ≤ 1 / 100) :
    AnalyticAt ℂ (fun y => highSolve K u ell (V y) (e y)) x := by
  have hR := (D.analyticAt_highInverse V e x hV he hs hd).contDiffAt (n := ω)
  exact (contDiffAt_const.clm_comp (hR.clm_comp contDiffAt_const)).analyticAt

include D in
theorem analyticAt_numerator (V : X → H →L[ℂ] H) (e : X → ℂ) (x : X)
    (hV : AnalyticAt ℂ V x) (he : AnalyticAt ℂ e x)
    (hs : ‖V x‖ ≤ 1 / 256) (hd : ‖e x - (ell : ℂ)‖ ≤ 1 / 100) :
    AnalyticAt ℂ (fun y => numerator K u ell (V y) (e y)) x := by
  have hH := (D.analyticAt_highSolve V e x hV he hs hd).contDiffAt (n := ω)
  exact (contDiffAt_const.add
    (contDiffAt_const.clm_comp (hV.contDiffAt.clm_comp hH))).analyticAt

include D in
theorem analyticAt_rankOneNumerator (V : X → H →L[ℂ] H) (e : X → ℂ) (x : X)
    (hV : AnalyticAt ℂ V x) (he : AnalyticAt ℂ e x)
    (hs : ‖V x‖ ≤ 1 / 256) (hd : ‖e x - (ell : ℂ)‖ ≤ 1 / 100) :
    AnalyticAt ℂ (fun y => rankOneNumerator K u ell (V y) (e y)) x := by
  have hN := (D.analyticAt_numerator V e x hV he hs hd).contDiffAt (n := ω)
  have hL := (D.analyticAt_eigenvectorLift V e x hV he hs hd).contDiffAt (n := ω)
  have hsmooth : ContDiff ℂ ω (ContinuousLinearMap.smulRightL ℂ H H) :=
    ContinuousLinearMap.contDiff (𝕜 := ℂ) (E := H →L[ℂ] ℂ)
      (F := H →L[ℂ] (H →L[ℂ] H)) (ContinuousLinearMap.smulRightL ℂ H H)
  have hS := hsmooth.contDiffAt.comp x hN
  exact (hS.clm_apply hL).analyticAt

include D in
theorem analyticAt_scalarResidual (V : X → H →L[ℂ] H) (e : X → ℂ) (x : X)
    (hV : AnalyticAt ℂ V x) (he : AnalyticAt ℂ e x)
    (hs : ‖V x‖ ≤ 1 / 256) (hd : ‖e x - (ell : ℂ)‖ ≤ 1 / 100) :
    AnalyticAt ℂ (fun y => scalarResidual K u ell (V y) (e y)) x :=
  (D.analyticAt_rootMap V e x hV he hs hd).sub he

include D in
theorem analyticAt_resolvent (V : X → H →L[ℂ] H) (e : X → ℂ) (x : X)
    (hV : AnalyticAt ℂ V x) (he : AnalyticAt ℂ e x)
    (hs : ‖V x‖ ≤ 1 / 256) (hd : ‖e x - (ell : ℂ)‖ ≤ 1 / 100)
    (hg : scalarResidual K u ell (V x) (e x) ≠ 0) :
    AnalyticAt ℂ (fun y => resolvent K u ell (V y) (e y)) x := by
  have hG := (D.analyticAt_scalarResidual V e x hV he hs hd).inv hg
  have hN := D.analyticAt_rankOneNumerator V e x hV he hs hd
  have hH := D.analyticAt_highSolve V e x hV he hs hd
  exact ((hG.contDiffAt.smul hN.contDiffAt).sub hH.contDiffAt).analyticAt

#print axioms analyticAt_resolvent
#print axioms analyticAt_rankOneNumerator

end Maxwell.Continuum.RankOneBand.Data
