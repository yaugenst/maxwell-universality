import Maxwell.Defect.PhysicalLimitConstruction
import Maxwell.Certificate.PointWitness.ConventionalPhysical

/-! The frozen conventional Maxwell eigenbranch gives the actual
square-root expansion of every finite weighted source compression. -/
namespace Maxwell.Defect.PhysicalLimit
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Spectral.Bloch
open Maxwell.Green Maxwell.Green.SourceProfile
open Maxwell.Certificate Maxwell.Certificate.PointWitness
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology
noncomputable section
variable {N : ℕ}
set_option maxHeartbeats 1600000

theorem conventional_real_value
    (value : ConventionalAnalytic.ComplexMomentum → ℂ)
    (hreal : ∀ᶠ q : PeriodicYee.Momentum in 𝓝 0,
      (value (conventionalRealDisplacement q)).im = 0) :
    ∀ᶠ q : Momentum in 𝓝 0,
      value (momentumComplex q) = ((pointEnergy + conventionalDispersion value q : ℝ) : ℂ) := by
  have hc : Continuous (primitivePhysicalDirection : Momentum → PeriodicYee.Momentum) := by
    unfold primitivePhysicalDirection
    fun_prop
  have ht : Tendsto primitivePhysicalDirection (𝓝 (0 : Momentum)) (𝓝 0) := by
    simpa only [primitivePhysicalDirection, WithLp.ofLp_zero, smul_zero] using
      hc.continuousAt.tendsto (x := (0 : Momentum))
  filter_upwards [ht.eventually hreal] with q hq
  have he : conventionalRealDisplacement (primitivePhysicalDirection q) = momentumComplex q := by
    have hh := primitivePhysicalDirection_ray q 1
    simp only [one_smul] at hh
    exact hh.trans (by ext j; rfl)
  rw [he] at hq
  apply Complex.ext
  · change (value (momentumComplex q)).re =
      pointEnergy + ((value (momentumComplex q)).re - pointEnergy)
    ring
  · exact hq.trans (Complex.ofReal_im _).symm

/-- All premises here are properties of the single finite conventional
branch, returned together by `exists_conventional_physical_edge_data`.
The limiting infinite compression, its coefficient, and its remainder
are conclusions. -/
theorem conventional_compression_sqrt_limit (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (S : PhysicalSimpleEdgeData Concrete.material pointEnergy conventionalPointMomentum)
    (hlower : ∀ q : Momentum, ‖q‖^2 / 12000 ≤ momentumHessian S.value 0 q q)
    (heven : ∀ᶠ q : Momentum in 𝓝 0,
      conventionalDispersion S.value (-q) = conventionalDispersion S.value q)
    (hreal : ∀ᶠ q : PeriodicYee.Momentum in 𝓝 0,
      (S.value (conventionalRealDisplacement q)).im = 0)
    (halg : ∀ᶠ z in 𝓝 (0 : ConventionalAnalytic.ComplexMomentum),
      S.projector z * S.projector z = S.projector z ∧
      conventionalPointOperator z * S.projector z = S.value z • S.projector z ∧
      S.projector z * conventionalPointOperator z = S.value z • S.projector z)
    (haug : ∀ᶠ z in 𝓝 (0 : ConventionalAnalytic.ComplexMomentum),
      (conventionalPointOperator z - (pointEnergy : ℂ) • 1 + S.projector z).IsInvertible)
    (K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient (PeriodicYee.edgeAverage Concrete.material) e| ≤ K) :
    ∃ (S₀ : LocalOperator (N := N)) (κ R r : ℝ), 0 < κ ∧ 0 ≤ R ∧ 0 < r ∧
      IsSelfAdjoint S₀ ∧
      (∀ ξ : ℝ, 0 < ξ → ξ < r →
        ‖S₀ - compression edges W (PeriodicYee.edgeAverage Concrete.material) K hK hm (pointEnergy - ξ) -
          (κ * Real.sqrt ξ) • rankOne ℂ
            ((localSource edges W (angularTorusPoint conventionalPointMomentum) 0).adjoint S.eigenvector)
            ((localSource edges W (angularTorusPoint conventionalPointMomentum) 0).adjoint S.eigenvector)‖ ≤ R * ξ) ∧
      Tendsto (fun ξ => compression edges W (PeriodicYee.edgeAverage Concrete.material) K hK hm (pointEnergy - ξ))
        (𝓝[>] 0) (𝓝 S₀) := by
  let d := conventionalDispersion S.value
  obtain ⟨p, hp⟩ := conventionalDispersion_analytic S.value S.value_analytic
  let B := (1 / 2 : ℝ) • momentumHessian S.value 0
  have hB (x y : Momentum) : B x y = B y x := by
    change (1 / 2 : ℝ) * momentumHessian S.value 0 x y =
      (1 / 2 : ℝ) * momentumHessian S.value 0 y x
    rw [momentumHessian_symmetric S.value 0 S.value_analytic x y]
  have hpB (q : Momentum) : p 2 (fun _ => q) = B q q := by
    rw [powerSeries_two_eq_half_ray _ p hp q,
      conventionalDispersion_second_eq_momentumHessian S.value S.value_analytic q]
    rfl
  have hc (q : Momentum) : (1 / 24000 : ℝ) * ‖q‖^2 ≤ B q q := by
    change _ ≤ (1 / 2 : ℝ) * momentumHessian S.value 0 q q
    linarith [hlower q]
  have hT (q : Momentum) :
      fiber (PeriodicYee.edgeAverage Concrete.material) (angularTorusPoint conventionalPointMomentum) q =
        conventionalPointOperator (momentumComplex q) :=
    fiber_conventional Concrete.material conventionalPointMomentum q
  have ht : Tendsto momentumComplexCLM (𝓝 (0 : Momentum)) (𝓝 0) :=
    momentumComplexCLM.continuous.continuousAt.tendsto
  have hA : ∀ᶠ q : Momentum in 𝓝 0,
      let P := S.projector (momentumComplex q)
      let T := fiber (PeriodicYee.edgeAverage Concrete.material) (angularTorusPoint conventionalPointMomentum) q
      P * P = P ∧ T * P = ((pointEnergy + d q : ℝ) : ℂ) • P ∧
        P * T = ((pointEnergy + d q : ℝ) : ℂ) • P := by
    filter_upwards [ht.eventually halg, conventional_real_value S.value hreal] with q hq hv
    dsimp only
    rw [hT, ← hv]
    exact hq
  have hi0 : (fiber (PeriodicYee.edgeAverage Concrete.material)
      (angularTorusPoint conventionalPointMomentum) 0 - (pointEnergy : ℂ) • 1 + S.projector 0).IsInvertible := by
    rw [hT, show momentumComplex (0 : Momentum) = 0 from map_zero momentumComplexCLM]
    exact haug.self_of_nhds
  obtain ⟨C, L, r, hL, hr, _, hC0, _, hdecomp, hreg⟩ := exists_physical_limit_data
    edges W Concrete.material pointEnergy conventionalPointMomentum S K hK hm d p hp
    (conventionalDispersion_zero S.value S.value_zero) heven B hB hpB
    (1 / 24000) (by norm_num) hc hA hi0
  let S₀ := edgeLimit edges W (PeriodicYee.edgeAverage Concrete.material)
    (angularTorusPoint conventionalPointMomentum) (fun q => S.projector (momentumComplex q)) pointEnergy C
  have hlim : Tendsto (fun ξ => compression edges W (PeriodicYee.edgeAverage Concrete.material)
      K hK hm (pointEnergy - ξ)) (𝓝[>] 0) (𝓝 S₀) :=
    compression_tendsto_edge edges W (PeriodicYee.edgeAverage Concrete.material) K hK hm
      (angularTorusPoint conventionalPointMomentum) (fun q => S.projector (momentumComplex q))
      pointEnergy L r hr C hdecomp (fun ξ hξ hξr => hreg ξ hξ.le hξr)
  have hnum : C.edgeNumerator = rankOne ℂ
      ((localSource edges W (angularTorusPoint conventionalPointMomentum) 0).adjoint S.eigenvector)
      ((localSource edges W (angularTorusPoint conventionalPointMomentum) 0).adjoint S.eigenvector) := by
    rw [hC0, numerator, show momentumComplex (0 : Momentum) = 0 from map_zero momentumComplexCLM,
      S.projector_zero, sourceCompression_rankOne]
  refine ⟨S₀, C.edgeCoefficient, (C.localRemainder + L) / (2 * Real.pi)^3, r,
    C.edgeCoefficient_pos, div_nonneg (add_nonneg C.localRemainder_nonneg hL) (by positivity),
    hr, edgeLimit_selfAdjoint edges W (PeriodicYee.edgeAverage Concrete.material) K hK hm
      (angularTorusPoint conventionalPointMomentum) (fun q => S.projector (momentumComplex q))
      pointEnergy C hlim, ?_, hlim⟩
  intro ξ hξ hξr
  rw [← hnum]
  exact physical_sqrt_expansion edges W (PeriodicYee.edgeAverage Concrete.material) K hK hm
    (angularTorusPoint conventionalPointMomentum) (fun q => S.projector (momentumComplex q))
    pointEnergy ξ L C hξ (hdecomp ξ hξ hξr) (hreg ξ hξ.le hξr)

end
end Maxwell.Defect.PhysicalLimit
