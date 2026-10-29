import Maxwell.Continuum.RankOneBandFamilyAnalytic
import Maxwell.Continuum.RankOneBandQuadraticDerivative

/-! The first two derivatives of the actual affine eigenvalue branch are
derived from its fixed-point identity. The second coefficient is the
literal high-space inverse quadratic form. -/

noncomputable section
namespace Maxwell.Continuum.RankOneBand

set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped NNReal Topology ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : H →L[ℂ] H} {u : H} {ell : ℝ}

def affinePerturbation (W : H →L[ℂ] H) (z _e : ℂ) : H →L[ℂ] H := z • W

omit [CompleteSpace H] in
theorem affinePerturbation_analytic (W : H →L[ℂ] H) (S : Set (ℂ × ℂ)) :
    AnalyticOnNhd ℂ (Function.uncurry (affinePerturbation W)) S := by
  intro p _hp
  exact (contDiffAt_fst.smul contDiffAt_const :
    ContDiffAt ℂ ω (fun q : ℂ × ℂ => q.1 • W) p).analyticAt

omit [CompleteSpace H] in
theorem highOperator_zero : highOperator K u ell 0 (ell : ℂ) = baseHigh K u ell := by
  apply ContinuousLinearMap.ext
  intro x
  simp [highOperator, highPerturbation, compress]

namespace Data

variable (D : Data K u ell)

theorem highInverse_zero : highInverse K u ell 0 (ell : ℂ) = D.baseInverse := by
  apply ContinuousLinearMap.ext
  intro x
  apply (ContinuousLinearMap.isUnit_iff_bijective.mp
    (CoerciveInverse.isUnit (baseHigh K u ell) (by norm_num : (0 : ℝ) < 1 / 20)
      D.baseHigh_coercive)).1
  have h := D.highOperator_inverse_apply (0 : H →L[ℂ] H) (ell : ℂ)
    (by norm_num) (by simp) x
  rw [highOperator_zero] at h
  rw [h]
  exact (CoerciveInverse.apply_inverse (baseHigh K u ell)
    (by norm_num : (0 : ℝ) < 1 / 20) D.baseHigh_coercive x).symm

variable (W : H →L[ℂ] H) {f : ℂ → ℂ}

/-- Differentiating the literal local scalar Schur identity gives both
derivatives. The analytic branch may be any slice of the already-constructed
multivariate band; no separate fixed-point construction is required. -/
theorem affine_branch_derivatives (hf : AnalyticAt ℂ f 0) (h0 : f 0 = (ell : ℂ))
    (hroot : ∀ᶠ z in 𝓝 0, rootMap K u ell (z • W) (f z) = f z) :
    deriv f 0 = coefficient u (W u) ∧
    deriv (deriv f) 0 =
      2 * coefficient u (W (embed u (D.baseInverse (project u (W u))))) := by
  let b : ℂ → ℂ := fun z =>
    coefficient u (W (embed u (highInverse K u ell (z • W) (f z) (project u (W u)))))
  have hV : AnalyticAt ℂ (fun z : ℂ => z • W) 0 :=
    (contDiffAt_id.smul contDiffAt_const : ContDiffAt ℂ ω (fun z : ℂ => z • W) 0).analyticAt
  have hR := D.analyticAt_highInverse (fun z : ℂ => z • W) f 0 hV hf
    (by simp) (by rw [h0, sub_self, norm_zero]; norm_num)
  have hRc : ContDiffAt ℂ ω
      (fun z : ℂ => highInverse K u ell (z • W) (f z) (project u (W u))) 0 :=
    hR.contDiffAt.clm_apply contDiffAt_const
  have hb : AnalyticAt ℂ b 0 :=
    ((coefficient u).contDiff.contDiffAt.comp 0 (W.contDiff.contDiffAt.comp 0
    ((embed u).contDiff.contDiffAt.comp 0 hRc))).analyticAt
  have heq : f =ᶠ[𝓝 0] fun z => (ell : ℂ) + coefficient u (W u) * z + z ^ 2 * b z := by
    filter_upwards [hroot] with z hz
    unfold rootMap correctionVector at hz
    simp only [smul_apply, map_smul] at hz
    change (ell : ℂ) + z * coefficient u (W u) + z * (z * b z) = f z at hz
    rw [← hz]
    ring
  have hb0 : b 0 = coefficient u (W (embed u (D.baseInverse (project u (W u))))) := by
    dsimp only [b]
    rw [zero_smul, h0, D.highInverse_zero]
  have h := quadratic_derivatives hb heq
  rwa [hb0] at h

include D in
theorem affine_branch_stationary (hf : AnalyticAt ℂ f 0) (h0 : f 0 = (ell : ℂ))
    (hroot : ∀ᶠ z in 𝓝 0, rootMap K u ell (z • W) (f z) = f z)
    (hW : inner ℂ u (W u) = 0) : deriv f 0 = 0 := by
  rw [(D.affine_branch_derivatives W hf h0 hroot).1]
  exact hW

theorem affine_branch_half_second (hf : AnalyticAt ℂ f 0) (h0 : f 0 = (ell : ℂ))
    (hroot : ∀ᶠ z in 𝓝 0, rootMap K u ell (z • W) (f z) = f z) :
    (1 / 2 : ℂ) * deriv (deriv f) 0 =
      inner ℂ u (W (embed u (D.baseInverse (project u (W u))))) := by
  rw [(D.affine_branch_derivatives W hf h0 hroot).2]
  change (1 / 2 : ℂ) * (2 * coefficient u _) = coefficient u _
  ring

#print axioms affine_branch_derivatives
#print axioms affine_branch_half_second

end Data
end Maxwell.Continuum.RankOneBand
