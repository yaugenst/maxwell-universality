import Maxwell.Continuum.RankOneBandBounds
import Maxwell.Continuum.AnalyticFixedPointScalar

/-! Analyticity of the literal inverse, scalar Schur map and eigenvector lift.
The inverse is the same total ring inverse used in the quantitative identities. -/

noncomputable section
namespace Maxwell.Continuum.RankOneBand

set_option backward.isDefEq.respectTransparency false

open scoped ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {K : H →L[ℂ] H} {u : H} {ell : ℝ}

theorem analyticAt_highOperator (V : X → H →L[ℂ] H) (e : X → ℂ) (x : X)
    (hV : AnalyticAt ℂ V x) (he : AnalyticAt ℂ e x) :
    AnalyticAt ℂ (fun y => highOperator K u ell (V y) (e y)) x := by
  let _ : NormSMulClass ℂ (highSpace u →L[ℂ] highSpace u) :=
    NormedSpace.toNormSMulClass (𝕜 := ℂ) (E := highSpace u →L[ℂ] highSpace u)
  have hVs : ContDiffAt ℂ ω V x := hV.contDiffAt
  have hes : ContDiffAt ℂ ω e x := he.contDiffAt
  have hc : ContDiffAt ℂ ω (fun y => compress u (V y)) x := by
    have hh : ContDiff ℂ ω (compression u) :=
      ContinuousLinearMap.contDiff (𝕜 := ℂ) (E := H →L[ℂ] H)
        (F := highSpace u →L[ℂ] highSpace u) (compression u)
    exact hh.contDiffAt.comp x hVs
  exact (contDiffAt_const.add
    (((hes.sub contDiffAt_const).smul contDiffAt_const).sub hc)).analyticAt

namespace Data

variable (D : Data K u ell)

include D in
theorem analyticAt_highInverse (V : X → H →L[ℂ] H) (e : X → ℂ) (x : X)
    (hV : AnalyticAt ℂ V x) (he : AnalyticAt ℂ e x)
    (hsmall : ‖V x‖ ≤ 1 / 256) (hdisk : ‖e x - (ell : ℂ)‖ ≤ 1 / 100) :
    AnalyticAt ℂ (fun y => highInverse K u ell (V y) (e y)) x := by
  have hunit := D.highOperator_isUnit (V x) (e x) hsmall hdisk
  have hi : AnalyticAt ℂ Ring.inverse (highOperator K u ell (V x) (e x)) := by
    simpa only [IsUnit.unit_spec] using
      analyticAt_inverse (𝕜 := ℂ) (A := highSpace u →L[ℂ] highSpace u) hunit.unit
  exact hi.comp (f := fun y => highOperator K u ell (V y) (e y))
    (analyticAt_highOperator V e x hV he)

include D in
theorem analyticAt_correctionVector (V : X → H →L[ℂ] H) (e : X → ℂ) (x : X)
    (hV : AnalyticAt ℂ V x) (he : AnalyticAt ℂ e x)
    (hsmall : ‖V x‖ ≤ 1 / 256) (hdisk : ‖e x - (ell : ℂ)‖ ≤ 1 / 100) :
    AnalyticAt ℂ (fun y => correctionVector K u ell (V y) (e y)) x := by
  have hVs : ContDiffAt ℂ ω V x := hV.contDiffAt
  have hR : ContDiffAt ℂ ω (fun y => highInverse K u ell (V y) (e y)) x :=
    (D.analyticAt_highInverse V e x hV he hsmall hdisk).contDiffAt
  exact ((embed u).contDiff.contDiffAt.comp x
    (hR.clm_apply ((project u).contDiff.contDiffAt.comp x
      (hVs.clm_apply contDiffAt_const)))).analyticAt

include D in
theorem analyticAt_rootMap (V : X → H →L[ℂ] H) (e : X → ℂ) (x : X)
    (hV : AnalyticAt ℂ V x) (he : AnalyticAt ℂ e x)
    (hsmall : ‖V x‖ ≤ 1 / 256) (hdisk : ‖e x - (ell : ℂ)‖ ≤ 1 / 100) :
    AnalyticAt ℂ (fun y => rootMap K u ell (V y) (e y)) x := by
  have hVs : ContDiffAt ℂ ω V x := hV.contDiffAt
  have hc : ContDiffAt ℂ ω (fun y => correctionVector K u ell (V y) (e y)) x :=
    (D.analyticAt_correctionVector V e x hV he hsmall hdisk).contDiffAt
  exact ((contDiffAt_const.add
    ((coefficient u).contDiff.contDiffAt.comp x (hVs.clm_apply contDiffAt_const))).add
    ((coefficient u).contDiff.contDiffAt.comp x (hVs.clm_apply hc))).analyticAt

include D in
theorem analyticAt_eigenvectorLift (V : X → H →L[ℂ] H) (e : X → ℂ) (x : X)
    (hV : AnalyticAt ℂ V x) (he : AnalyticAt ℂ e x)
    (hsmall : ‖V x‖ ≤ 1 / 256) (hdisk : ‖e x - (ell : ℂ)‖ ≤ 1 / 100) :
    AnalyticAt ℂ (fun y => eigenvectorLift K u ell (V y) (e y)) x :=
  analyticAt_const.add (D.analyticAt_correctionVector V e x hV he hsmall hdisk)

#print axioms analyticAt_highInverse
#print axioms analyticAt_rootMap
#print axioms analyticAt_eigenvectorLift

end Data
end Maxwell.Continuum.RankOneBand
