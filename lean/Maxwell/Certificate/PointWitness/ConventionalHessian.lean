import Maxwell.Certificate.PointWitness.ConventionalBranch
import Maxwell.Certificate.PointWitness.BranchJet
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

namespace Maxwell.Certificate.PointWitness

open Maxwell.Spectral Filter
open scoped Topology
noncomputable section

/-- Restriction to the real axis commutes with taking the real part of the
second derivative of a holomorphic scalar germ. -/
theorem analytic_real_second_derivative (f : ℂ → ℂ) (hf : AnalyticAt ℂ f 0) :
    deriv (deriv (fun t : ℝ => (f t).re)) 0 = (deriv (deriv f) 0).re := by
  have ht : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝 0) (𝓝 (0 : ℂ)) := by
    simpa only [Complex.ofReal_zero] using Complex.continuous_ofReal.continuousAt.tendsto (x := 0)
  have he : deriv (fun t : ℝ => (f t).re) =ᶠ[𝓝 (0 : ℝ)]
      fun t => (deriv f (t : ℂ)).re := by
    filter_upwards [ht.eventually hf.eventually_analyticAt] with t htf
    exact htf.differentiableAt.hasDerivAt.real_of_complex.deriv
  rw [he.deriv_eq]
  exact hf.deriv.differentiableAt.hasDerivAt.real_of_complex.deriv

abbrev PhysicalMomentum := EuclideanSpace ℝ (Fin 3)

def conventionalRealEmbedding : PhysicalMomentum →L[ℝ] ConventionalAnalytic.ComplexMomentum :=
  ContinuousLinearMap.pi fun j => Complex.ofRealCLM.comp (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j)

theorem conventionalRealEmbedding_apply (q : PhysicalMomentum) :
    conventionalRealEmbedding q = ConventionalAnalytic.realMomentum (WithLp.ofLp q) := rfl

/-- The physical dispersion in conventional angular momentum, measured from
the certified edge energy. Its domain has the Euclidean norm used by the
three-dimensional Green integral. -/
def conventionalDispersion (value : ConventionalAnalytic.ComplexMomentum → ℂ)
    (q : PhysicalMomentum) : ℝ := (value (conventionalRealEmbedding q)).re - pointEnergy

theorem conventionalDispersion_analytic
    (value : ConventionalAnalytic.ComplexMomentum → ℂ) (hv : AnalyticAt ℂ value 0) :
    AnalyticAt ℝ (conventionalDispersion value) 0 := by
  have hc : AnalyticAt ℝ (fun q => value (conventionalRealEmbedding q)) 0 :=
    (hv.restrictScalars (𝕜 := ℝ)).comp_of_eq (conventionalRealEmbedding.analyticAt 0) (map_zero _)
  exact ((Complex.reCLM.analyticAt _).comp hc).sub analyticAt_const

theorem conventionalDispersion_zero
    (value : ConventionalAnalytic.ComplexMomentum → ℂ) (hv0 : value 0 = (pointEnergy : ℂ)) :
    conventionalDispersion value 0 = 0 := by
  simp only [conventionalDispersion, map_zero, hv0, Complex.ofReal_re, sub_self]

theorem conventionalDispersion_even
    (value : ConventionalAnalytic.ComplexMomentum → ℂ)
    (heven : ∀ᶠ q : PeriodicYee.Momentum in 𝓝 0,
      value (-ConventionalAnalytic.realMomentum q) = value (ConventionalAnalytic.realMomentum q)) :
    ∀ᶠ q : PhysicalMomentum in 𝓝 0,
      conventionalDispersion value (-q) = conventionalDispersion value q := by
  have hc : Continuous (WithLp.ofLp : PhysicalMomentum → PeriodicYee.Momentum) := by fun_prop
  have ht : Tendsto (WithLp.ofLp : PhysicalMomentum → PeriodicYee.Momentum) (𝓝 0) (𝓝 0) :=
    hc.continuousAt.tendsto
  filter_upwards [ht.eventually heven] with q hq
  simp only [conventionalDispersion, map_neg, conventionalRealEmbedding_apply]
  exact congrArg (fun z : ℂ => z.re - pointEnergy) hq

def primitivePhysicalDirection (q : PhysicalMomentum) : PeriodicYee.Momentum :=
  (2 * Real.pi)⁻¹ • WithLp.ofLp q

theorem primitivePhysicalDirection_radius (q : PhysicalMomentum) :
    YeeTaylor.radius (primitivePhysicalDirection q) = (2 * Real.pi)⁻¹ * ‖q‖ := by
  change ‖(2 * Real.pi)⁻¹ • q‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by positivity))]

theorem primitivePhysicalDirection_curvature_scale (q : PhysicalMomentum) :
    YeeTaylor.radius (primitivePhysicalDirection q)^2 / 25 = ‖q‖^2 / (100 * Real.pi^2) := by
  rw [primitivePhysicalDirection_radius]
  field_simp
  ring

/-- This is precisely the finite compressed quadratic form required from the
H₁/H₂ certificate; it is not a Hessian assumption on a selected branch. -/
def PointCompressedLower (hgap : PointClusterComplementGap) : Prop :=
  ∀ (q : PeriodicYee.Momentum) (x : EuclideanSpace ℂ (Fin 2)),
    YeeTaylor.radius q^2 * ‖x‖^2 / 50 ≤ (inner ℂ x (pointCompressedJet hgap q x)).re

theorem pointCompressedLower_of_finiteJetBounds (hgap : PointClusterComplementGap)
    (δ : ℝ) (hjet : ∀ q : PeriodicYee.Momentum,
      FiniteJetBounds (pointTaylorCoefficient q) (pointExactIsometry hgap).toContinuousLinearMap
        (pointCorrector hgap q) (YeeTaylor.radius q) δ pointEnergy) :
    PointCompressedLower hgap :=
  fun q x => (hjet q).compressedLower x

theorem pointBranch_second_lower_of_compressed (hgap : PointClusterComplementGap)
    (hcompressed : PointCompressedLower hgap)
    (value : YeeAnalytic.ComplexMomentum → ℂ) (u : YeeAnalytic.ComplexMomentum → PointSpace)
    (hv : AnalyticAt ℂ value 0) (hu : AnalyticAt ℂ u 0)
    (hsolve : ∀ᶠ w in 𝓝 (0 : YeeAnalytic.ComplexMomentum),
      pointHolomorphicOperator w (u w) = value w • u w)
    (hv0 : value 0 = (pointEnergy : ℂ)) (hu0 : u 0 = pointEigenbasis pointIndex0)
    (hnorm : ∀ w, inner ℂ (pointEigenbasis pointIndex0) (u w) = 1)
    (heven : ∀ᶠ w in 𝓝 (0 : YeeAnalytic.ComplexMomentum), value (-w) = value w)
    (q : PeriodicYee.Momentum) :
    YeeTaylor.radius q^2 / 25 ≤
      (deriv (deriv (fun t : ℂ => value (t • YeeAnalytic.realMomentum q))) 0).re := by
  rw [pointAnalyticBranch_ray_second_derivative hgap value u hv hu hsolve hv0 hu0 hnorm heven q]
  have hl := hcompressed q (pointCenterCoordinates hgap)
  rw [pointCenterCoordinates_norm, one_pow, mul_one] at hl
  norm_num [Complex.mul_re]
  linarith

theorem primitivePhysicalDirection_ray (q : PhysicalMomentum) (t : ℝ) :
    conventionalRealDisplacement (t • primitivePhysicalDirection q) =
      conventionalRealEmbedding (t • q) := by
  have hp : 2 * Real.pi ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hs : (2 * Real.pi) • primitivePhysicalDirection q = WithLp.ofLp q := by
    rw [primitivePhysicalDirection, smul_smul, mul_inv_cancel₀ hp, one_smul]
  unfold conventionalRealDisplacement
  rw [smul_comm (2 * Real.pi) t, hs]
  rfl

/-- The same conventional branch has the certified curvature, after the
physical change of variables κ=q/(2π). The only numerical form input is the
actual compressed H₁/H₂ inequality. -/
theorem conventionalDispersion_ray_second_lower
    (hgap : PointClusterComplementGap) (hcompressed : PointCompressedLower hgap)
    (fullValue primitiveValue : YeeAnalytic.ComplexMomentum → ℂ)
    (u : YeeAnalytic.ComplexMomentum → PointSpace)
    (hv : AnalyticAt ℂ primitiveValue 0) (hu : AnalyticAt ℂ u 0)
    (hsolve : ∀ᶠ w in 𝓝 (0 : YeeAnalytic.ComplexMomentum),
      pointHolomorphicOperator w (u w) = primitiveValue w • u w)
    (hv0 : primitiveValue 0 = (pointEnergy : ℂ)) (hu0 : u 0 = pointEigenbasis pointIndex0)
    (hnorm : ∀ w, inner ℂ (pointEigenbasis pointIndex0) (u w) = 1)
    (heven : ∀ᶠ w in 𝓝 (0 : YeeAnalytic.ComplexMomentum), primitiveValue (-w) = primitiveValue w)
    (hres : ∀ᶠ z in 𝓝 ((0, 0) : ConventionalAnalytic.ComplexMomentum × ℂ),
      fullValue z.1 ≠ (pointEnergy : ℂ) + z.2 →
        (conventionalPointOperator z.1 - ((pointEnergy : ℂ) + z.2) • 1).IsInvertible)
    (q : PhysicalMomentum) :
    ‖q‖^2 / (100 * Real.pi^2) ≤
      deriv (deriv (fun t : ℝ => conventionalDispersion fullValue (t • q))) 0 := by
  have hn : ∀ᶠ w in 𝓝 (0 : YeeAnalytic.ComplexMomentum), u w ≠ 0 := by
    apply Eventually.of_forall
    intro w hz
    have hh := hnorm w
    rw [hz, inner_zero_right] at hh
    norm_num at hh
  have hid := conventional_point_branch_identification fullValue primitiveValue u
    hv.continuousAt hv0 hn hsolve hres
  let κ := primitivePhysicalDirection q
  have ht : Tendsto (fun t : ℝ => t • κ) (𝓝 0) (𝓝 (0 : PeriodicYee.Momentum)) := by
    have hc : Continuous (fun t : ℝ => t • κ) := continuous_id.smul continuous_const
    simpa only [zero_smul] using hc.continuousAt.tendsto (x := (0 : ℝ))
  have heq : (fun t : ℝ => conventionalDispersion fullValue (t • q)) =ᶠ[𝓝 0]
      fun t => (primitiveValue ((t : ℂ) • YeeAnalytic.realMomentum κ)).re - pointEnergy := by
    filter_upwards [ht.eventually hid] with t hh
    rw [primitivePhysicalDirection_ray] at hh
    have hp : YeeAnalytic.realMomentum (t • κ) = (t : ℂ) • YeeAnalytic.realMomentum κ := by
      ext j
      simp [YeeAnalytic.realMomentum]
    rw [hp] at hh
    exact congrArg (fun z : ℂ => z.re - pointEnergy) hh
  rw [heq.deriv.deriv_eq, deriv_sub_const_fun]
  have hray : AnalyticAt ℂ (fun t : ℂ => primitiveValue (t • YeeAnalytic.realMomentum κ)) 0 :=
    hv.comp_of_eq (analyticAt_id.smul analyticAt_const) (zero_smul _ _)
  rw [analytic_real_second_derivative _ hray]
  rw [← primitivePhysicalDirection_curvature_scale q]
  exact pointBranch_second_lower_of_compressed hgap hcompressed primitiveValue u hv hu hsolve
    hv0 hu0 hnorm heven κ

/-- The real ray second derivative is the diagonal of the actual second
Fréchet derivative, with no finite-difference or Hessian model assumption. -/
theorem ray_second_eq_iteratedFDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : AnalyticAt ℝ f 0) (q : E) :
    deriv (deriv (fun t : ℝ => f (t • q))) 0 =
      iteratedFDeriv ℝ 2 f 0 (fun _ => q) := by
  have hray : ContDiff ℝ 2 (fun t : ℝ => t • q) := contDiff_id.smul contDiff_const
  have hd : deriv (fun t : ℝ => t • q) = fun _ => q := by
    funext t
    simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const q).deriv
  have h := iteratedDeriv_vcomp_two
    (show ContDiffAt ℝ 2 f ((0 : ℝ) • q) by simpa only [zero_smul] using hf.contDiffAt)
    hray.contDiffAt
  simpa only [iteratedDeriv_succ, iteratedDeriv_zero, hd, deriv_const,
    zero_smul, map_zero, add_zero, Function.comp_def] using h

/-- The quadratic Taylor coefficient is half the diagonal second derivative.
This gives the coefficient interface used by `exists_analytic_localBandChart`. -/
theorem powerSeries_two_eq_half_ray {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (p : FormalMultilinearSeries ℝ E ℝ)
    (hp : HasFPowerSeriesAt f p 0) (q : E) :
    p 2 (fun _ => q) = (1/2 : ℝ) * deriv (deriv (fun t : ℝ => f (t • q))) 0 := by
  rw [ray_second_eq_iteratedFDeriv f hp.analyticAt q]
  obtain ⟨r, hr⟩ := hp
  have he := hr.factorial_smul q 2
  norm_num at he
  linarith

/-- The manuscript's weaker rational lower bound follows from the exact
angular-coordinate curvature constant. -/
theorem angular_curvature_ge_paper (q : PhysicalMomentum) :
    ‖q‖^2 / 12000 ≤ ‖q‖^2 / (100 * Real.pi^2) := by
  apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
  nlinarith [Real.pi_lt_four, Real.pi_pos]

section ActualHessian
variable (hgap : PointClusterComplementGap) (hcompressed : PointCompressedLower hgap)
    (fullValue primitiveValue : YeeAnalytic.ComplexMomentum → ℂ)
    (u : YeeAnalytic.ComplexMomentum → PointSpace)
    (hv : AnalyticAt ℂ primitiveValue 0) (hu : AnalyticAt ℂ u 0)
    (hsolve : ∀ᶠ w in 𝓝 (0 : YeeAnalytic.ComplexMomentum),
      pointHolomorphicOperator w (u w) = primitiveValue w • u w)
    (hv0 : primitiveValue 0 = (pointEnergy : ℂ)) (hu0 : u 0 = pointEigenbasis pointIndex0)
    (hnorm : ∀ w, inner ℂ (pointEigenbasis pointIndex0) (u w) = 1)
    (heven : ∀ᶠ w in 𝓝 (0 : YeeAnalytic.ComplexMomentum), primitiveValue (-w) = primitiveValue w)
    (hres : ∀ᶠ z in 𝓝 ((0, 0) : ConventionalAnalytic.ComplexMomentum × ℂ),
      fullValue z.1 ≠ (pointEnergy : ℂ) + z.2 →
        (conventionalPointOperator z.1 - ((pointEnergy : ℂ) + z.2) • 1).IsInvertible)

include hgap hcompressed primitiveValue u hv hu hsolve hv0 hu0 hnorm heven hres in
theorem conventionalDispersion_hessian_lower (hfull : AnalyticAt ℂ fullValue 0)
    (q : PhysicalMomentum) :
    ‖q‖^2 / (100 * Real.pi^2) ≤
      iteratedFDeriv ℝ 2 (conventionalDispersion fullValue) 0 (fun _ => q) := by
  rw [← ray_second_eq_iteratedFDeriv _ (conventionalDispersion_analytic fullValue hfull) q]
  exact conventionalDispersion_ray_second_lower hgap hcompressed fullValue primitiveValue u
    hv hu hsolve hv0 hu0 hnorm heven hres q

include hgap hcompressed primitiveValue u hv hu hsolve hv0 hu0 hnorm heven hres in
theorem conventionalDispersion_hessian_paper_lower (hfull : AnalyticAt ℂ fullValue 0)
    (q : PhysicalMomentum) :
    ‖q‖^2 / 12000 ≤
      iteratedFDeriv ℝ 2 (conventionalDispersion fullValue) 0 (fun _ => q) :=
  (angular_curvature_ge_paper q).trans
    (conventionalDispersion_hessian_lower hgap hcompressed fullValue primitiveValue u
      hv hu hsolve hv0 hu0 hnorm heven hres hfull q)

include hgap hcompressed primitiveValue u hv hu hsolve hv0 hu0 hnorm heven hres in
/-- The positive quadratic Taylor form required by the Green chart is
obtained from the actual same-branch Hessian, with the factorial accounted for. -/
theorem conventionalDispersion_quadratic_lower
    (p : FormalMultilinearSeries ℝ PhysicalMomentum ℝ)
    (hp : HasFPowerSeriesAt (conventionalDispersion fullValue) p 0)
    (q : PhysicalMomentum) :
    ‖q‖^2 / (200 * Real.pi^2) ≤ p 2 (fun _ => q) ∧
      ‖q‖^2 / 24000 ≤ p 2 (fun _ => q) := by
  have hl := conventionalDispersion_ray_second_lower hgap hcompressed fullValue primitiveValue u
    hv hu hsolve hv0 hu0 hnorm heven hres q
  have hpaper := (angular_curvature_ge_paper q).trans hl
  rw [powerSeries_two_eq_half_ray _ p hp q]
  have hscale : ‖q‖^2 / (200 * Real.pi^2) = (1/2 : ℝ) * (‖q‖^2 / (100 * Real.pi^2)) := by
    field_simp
    ring
  rw [hscale]
  constructor <;> linarith
end ActualHessian

end
end Maxwell.Certificate.PointWitness
