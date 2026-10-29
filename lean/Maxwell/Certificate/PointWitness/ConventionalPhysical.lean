import Maxwell.Certificate.PointWitness.VerifiedCurvature
import Maxwell.Certificate.PointWitness.ConventionalStationary
import Maxwell.Spectral.SimpleRegularization
import Maxwell.Green.PhysicalEdge

namespace Maxwell.Certificate.PointWitness

open Maxwell.Spectral Maxwell.Spectral.ConventionalAnalytic Maxwell.Green Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 600000

theorem conventionalDispersion_second_eq_momentumHessian
    (value : ComplexMomentum → ℂ) (hv : AnalyticAt ℂ value 0)
    (q : PhysicalMomentum) :
    deriv (deriv (fun t : ℝ => conventionalDispersion value (t • q))) 0 =
      momentumHessian value 0 q q := by
  let coords : RealTorusCoordinates := WithLp.ofLp q
  have hline (t : ℝ) : complexRealLine coords 0 t = conventionalRealEmbedding (t • q) := by
    ext i
    simp [complexRealLine, complexifyCoordinates, conventionalRealEmbedding,
      coords, smul_eq_mul]
  have hzero : complexRealLine coords 0 0 = 0 := by
    ext i
    simp [complexRealLine, complexifyCoordinates]
  have ht : Tendsto (complexRealLine coords 0) (𝓝 (0 : ℝ)) (𝓝 0) := by
    simpa only [hzero] using (continuous_complexRealLine coords 0).continuousAt.tendsto
      (x := (0 : ℝ))
  have heq : deriv (fun t : ℝ => conventionalDispersion value (t • q)) =ᶠ[𝓝 0]
      fun t => ((fderiv ℂ value (complexRealLine coords 0 t)) (complexifyCoordinates coords)).re := by
    filter_upwards [ht.eventually hv.eventually_analyticAt] with t hvt
    have hd := (hasDerivAt_realPart_line value coords 0 t hvt).sub_const pointEnergy
    simpa only [hline, conventionalDispersion] using hd.deriv
  rw [heq.deriv_eq]
  have hd := hasDerivAt_realPart_line_derivative value coords 0 0
    (by simpa only [hzero] using hv)
  have hh := hd.deriv
  rw [hzero, realDirectionForm_apply] at hh
  have hc : complexifyCoordinates coords = momentumComplex q := rfl
  rw [momentumHessian_apply, ← hc]
  exact hh

/-- The global real spectral exclusion still required from the finite
neighborhood and torus-cover certificates, stated on the actual full fiber. -/
def PointRealEdgeExclusion : Prop :=
  ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 →
    (conventionalPointOperator (realMomentum q) - (pointEnergy : ℂ) • 1).IsInvertible

theorem conventional_point_regularization
    (hgap : PointClusterComplementGap) (hexclude : PointOtherSectorExclusion)
    (P : ComplexMomentum → ConventionalPointSpace →L[ℂ] ConventionalPointSpace)
    (hP : ContinuousAt P 0)
    (hP0 : P 0 = (innerSL ℂ (conventionalPointVector hgap hexclude)).smulRight
      (conventionalPointVector hgap hexclude)) :
    ∀ᶠ z in 𝓝 (0 : ComplexMomentum),
      (conventionalPointOperator z - (pointEnergy : ℂ) • 1 + P z).IsInvertible := by
  have hi := SimpleSplitting.simple_regularization_invertible
    (Matrix.toEuclideanCLM (n := PeriodicYee.Electric20) (𝕜 := ℂ) conventionalPointFiber)
    conventionalPoint_symmetric (conventionalPointIndex hgap hexclude)
    (conventionalPointIndex_simple hgap hexclude)
  change (Matrix.toEuclideanCLM (n := PeriodicYee.Electric20) (𝕜 := ℂ) conventionalPointFiber -
    (conventionalPoint_symmetric.eigenvalues rfl (conventionalPointIndex hgap hexclude) : ℂ) • 1 +
      (innerSL ℂ (conventionalPointVector hgap hexclude)).smulRight
        (conventionalPointVector hgap hexclude)).IsInvertible at hi
  rw [conventionalPointIndex_energy] at hi
  have hi0 : (conventionalPointOperator 0 - (pointEnergy : ℂ) • 1 + P 0).IsInvertible := by
    simpa only [conventionalPointOperator_zero, hP0] using hi
  have hc : ContinuousAt (fun z => conventionalPointOperator z - (pointEnergy : ℂ) • 1 + P z) 0 :=
    (conventionalPointOperator_analytic.continuousAt.sub continuousAt_const).add hP
  exact hc.tendsto.eventually hi0.eventually_nhds

/-- All local analytic Green data come from one conventional branch of the
frozen operator. The only premises are the named finite spectral inputs;
the Hessian, reflection, stationary point and pole decomposition are derived. -/
theorem exists_conventional_physical_edge_data
    (hgap : PointClusterComplementGap) (hexclude : PointOtherSectorExclusion)
    (hglobal : PointRealEdgeExclusion) :
    ∃ S : PhysicalSimpleEdgeData Concrete.material pointEnergy conventionalPointMomentum,
      S.eigenvector = conventionalRealPointVector hgap hexclude ∧
      ‖S.eigenvector‖ = 1 ∧ (∀ i, (S.eigenvector i).im = 0) ∧
      (∀ q : PhysicalMomentum, ‖q‖^2 / 12000 ≤ momentumHessian S.value 0 q q) ∧
      (∀ᶠ q : PhysicalMomentum in 𝓝 0,
        conventionalDispersion S.value (-q) = conventionalDispersion S.value q) ∧
      (∀ᶠ q : PeriodicYee.Momentum in 𝓝 0,
        (S.value (conventionalRealDisplacement q)).im = 0) ∧
      (∀ᶠ z in 𝓝 (0 : ComplexMomentum),
        S.projector z * S.projector z = S.projector z ∧
        conventionalPointOperator z * S.projector z = S.value z • S.projector z ∧
        S.projector z * conventionalPointOperator z = S.value z • S.projector z) ∧
      (∀ᶠ z in 𝓝 (0 : ComplexMomentum),
        (conventionalPointOperator z - (pointEnergy : ℂ) • 1 + S.projector z).IsInvertible) := by
  have hcompressed := pointCompressedLower_verified hgap
  obtain ⟨pv, pu, pP, pR, hpv0, hpu0, _, hpv, hpu, _, _, hpn, hpg, _⟩ :=
    exists_even_point_analytic_resolvent hgap
  obtain ⟨value, u, P, R, hv0, _, hP0, hv, _, hP, hR, hg, hr⟩ :=
    exists_conventional_point_analytic_resolvent hgap hexclude
  have hpsolve := hpg.mono fun _ h => h.1
  have hpeven := hpg.mono fun _ h => h.2.1
  have hres := hr.mono fun _ h hne => (h hne).1
  have hnonzero := hg.mono fun _ h => h.1
  have hsolve := hg.mono fun _ h => h.2.1
  have hid := conventional_point_branch_identification value pv pu hpv.continuousAt hpv0
    (Eventually.of_forall fun w => (hpn w).2) hpsolve hres
  have hrealEven := conventional_point_standard_real_even value
    (conventional_point_real_even_of_identification value pv hid hpeven)
  have hlower (q : PhysicalMomentum) : ‖q‖^2 / 12000 ≤ momentumHessian value 0 q q := by
    have hh := conventionalDispersion_ray_second_lower hgap hcompressed value pv pu
      hpv hpu hpsolve hpv0 hpu0 (fun w => (hpn w).1) hpeven hres q
    rw [conventionalDispersion_second_eq_momentumHessian value hv q] at hh
    exact (angular_curvature_ge_paper q).trans hh
  let S : PhysicalSimpleEdgeData Concrete.material pointEnergy conventionalPointMomentum := {
    value := value
    projector := P
    regular := R
    eigenvector := conventionalRealPointVector hgap hexclude
    value_zero := hv0
    projector_zero := hP0.trans (conventionalRealPointVector_projector hgap hexclude).symm
    value_analytic := hv
    projector_analytic := hP
    regular_analytic := hR
    stationary := conventional_point_branch_stationary value hv hrealEven
    hessian_positive := fun q hq => (by positivity : (0 : ℝ) < ‖q‖^2 / 12000).trans_le (hlower q)
    reflection := conventional_point_branch_reflection value u hv.continuousAt hv0
      (hg.mono fun _ h => ⟨h.1, h.2.1⟩) hres
    resolvent := hr
    real_exclusion := hglobal }
  refine ⟨S, rfl, conventionalRealPointVector_norm hgap hexclude,
    conventionalRealPointVector_real hgap hexclude, hlower,
    conventionalDispersion_even value hrealEven,
    conventional_point_real_germ value u hnonzero hsolve,
    hg.mono (fun _ h => h.2.2), conventional_point_regularization hgap hexclude P hP.continuousAt hP0⟩

end
end Maxwell.Certificate.PointWitness
