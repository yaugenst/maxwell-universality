import Maxwell.Defect.ConventionalLimit
import Maxwell.Defect.NormalizedLocalEigenvector
import Maxwell.Defect.PhysicalNegativeGap
import Maxwell.Defect.PhysicalInverseBound
import Maxwell.Defect.CoherentCubeRayleigh

/-! A sufficiently large scalar cube has a strict high Rayleigh quotient
for the actual conventional edge compression. The local constants are
chosen from the finite eigenbranch before the cube size is selected. -/
namespace Maxwell.Defect.ScalarDefect

open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Spectral.Bloch
open Maxwell.Green Maxwell.Green.SourceProfile Maxwell.Green.PhysicalAnalytic
open Maxwell.Certificate Maxwell.Certificate.PointWitness
open Maxwell.Defect.PhysicalLimit
open Filter Set MeasureTheory InnerProductSpace
open scoped Topology

noncomputable section
set_option maxHeartbeats 1600000

theorem conventional_point_center_trim :
    angularTorusPoint conventionalPointMomentum +
      angularTorusPoint conventionalPointMomentum = 0 := by
  change Bloch.momentumTorus conventionalPointMomentum +
    Bloch.momentumTorus conventionalPointMomentum = 0
  rw [conventionalPointMomentum, pointPrimitiveMomentum, conventionalMomentum_trim]
  exact momentumTorus_trim (conventionalTrimCoordinates ![1, 1, 0])

/-- Source-independent local dispersion and unit eigenvector data from
the actual conventional branch. -/
theorem exists_conventional_coherent_chart
    (S : PhysicalSimpleEdgeData Concrete.material pointEnergy conventionalPointMomentum)
    (hu : ‖S.eigenvector‖ = 1)
    (hlower : ∀ q : Momentum, ‖q‖ ^ 2 / 12000 ≤ momentumHessian S.value 0 q q)
    (heven : ∀ᶠ q : Momentum in 𝓝 0,
      conventionalDispersion S.value (-q) = conventionalDispersion S.value q)
    (hreal : ∀ᶠ q : PeriodicYee.Momentum in 𝓝 0,
      (S.value (conventionalRealDisplacement q)).im = 0)
    (halg : ∀ᶠ z in 𝓝 (0 : ConventionalAnalytic.ComplexMomentum),
      S.projector z * S.projector z = S.projector z ∧
      conventionalPointOperator z * S.projector z = S.value z • S.projector z ∧
      S.projector z * conventionalPointOperator z = S.value z • S.projector z) :
    ∃ B : LocalBandChart ℝ, ∃ φ : Momentum → EuclideanSpace ℂ Edge20,
      ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ r ≤ B.radius ∧
        ContinuousOn φ (Metric.ball 0 r) ∧
        ∀ q ∈ Metric.ball 0 r,
          ‖φ q‖ = 1 ∧ ‖φ q - S.eigenvector‖ ≤ C * ‖q‖ ∧
          fiber (PeriodicYee.edgeAverage Concrete.material)
            (angularTorusPoint conventionalPointMomentum) q (φ q) =
              ((pointEnergy + B.dispersion q : ℝ) : ℂ) • φ q := by
  obtain ⟨p, hp⟩ := conventionalDispersion_analytic S.value S.value_analytic
  let Q := (1 / 2 : ℝ) • momentumHessian S.value 0
  have hQ (x y : Momentum) : Q x y = Q y x := by
    change (1 / 2 : ℝ) * momentumHessian S.value 0 x y =
      (1 / 2 : ℝ) * momentumHessian S.value 0 y x
    rw [momentumHessian_symmetric S.value 0 S.value_analytic x y]
  have hpQ (q : Momentum) : p 2 (fun _ => q) = Q q q := by
    rw [powerSeries_two_eq_half_ray _ p hp q,
      conventionalDispersion_second_eq_momentumHessian S.value S.value_analytic q]
    rfl
  have hc (q : Momentum) : (1 / 24000 : ℝ) * ‖q‖ ^ 2 ≤ Q q q := by
    change _ ≤ (1 / 2 : ℝ) * momentumHessian S.value 0 q q
    linarith [hlower q]
  obtain ⟨A, hA⟩ := exists_quadratic_root Q hQ (fun q hq =>
    (by positivity : (0 : ℝ) < (1 / 24000 : ℝ) * ‖q‖ ^ 2).trans_le (hc q))
  obtain ⟨B, _, _, _, _, hBd, _, _⟩ := exists_analytic_localBandChart
    (fun _ : Momentum => (0 : ℝ)) (conventionalDispersion S.value) p analyticAt_const hp
    (conventionalDispersion_zero S.value S.value_zero) heven A
    (c := 1 / 24000) (radiusLimit := 1) (by norm_num) (by norm_num)
    (fun q => (hpQ q).trans (hA q).symm) (fun q => (hc q).trans_eq (hA q).symm)
  let P := fun q : Momentum => S.projector (momentumComplex q)
  let T := fiber (PeriodicYee.edgeAverage Concrete.material)
    (angularTorusPoint conventionalPointMomentum)
  have hP : AnalyticAt ℝ P 0 := S.projector_analytic.restrictScalars.comp_of_eq
    (momentumComplexCLM.analyticAt 0) (map_zero momentumComplexCLM)
  have hP0 : P 0 = rankOne ℂ S.eigenvector S.eigenvector := by
    dsimp [P]
    rw [show momentumComplex (0 : Momentum) = 0 from map_zero momentumComplexCLM,
      S.projector_zero]
  have ht : Tendsto momentumComplexCLM (𝓝 (0 : Momentum)) (𝓝 0) :=
    momentumComplexCLM.continuous.continuousAt.tendsto
  have heig : ∀ᶠ q : Momentum in 𝓝 0, T q * P q =
      ((pointEnergy + conventionalDispersion S.value q : ℝ) : ℂ) • P q := by
    filter_upwards [ht.eventually halg, conventional_real_value S.value hreal] with q hq hv
    dsimp only [T, P]
    rw [fiber_conventional, ← hv]
    exact hq.2.1
  obtain ⟨rV, C, hrV, hC, _, hcont, hφ⟩ :=
    exists_normalized_local_eigenvector_of_projector T P
      (fun q => ((pointEnergy + conventionalDispersion S.value q : ℝ) : ℂ))
      S.eigenvector hP hu hP0 heig
  refine ⟨B, normalizedProjectorVector P S.eigenvector, min B.radius rV, C,
    lt_min B.radius_pos hrV, hC, min_le_left _ _,
    hcont.mono (Metric.ball_subset_ball (min_le_right _ _)), ?_⟩
  intro q hq
  have hqB := Metric.ball_subset_ball (min_le_left B.radius rV) hq
  obtain ⟨hn, he, hv⟩ := hφ q (Metric.ball_subset_ball (min_le_right B.radius rV) hq)
  refine ⟨hn, hv, ?_⟩
  rw [hBd q hqB]
  exact he

/-- The actual edge compression of one sufficiently large cube has a
strict high coherent Rayleigh quotient. Its square-root coefficient uses
the same physical eigenvector that defines the coherent source. -/
theorem exists_conventional_cube_high_rayleigh
    (S : PhysicalSimpleEdgeData Concrete.material pointEnergy conventionalPointMomentum)
    (hu : ‖S.eigenvector‖ = 1) (hureal : ∀ i, (S.eigenvector i).im = 0)
    (hlower : ∀ q : Momentum, ‖q‖ ^ 2 / 12000 ≤ momentumHessian S.value 0 q q)
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
    (threshold K : ℝ) (hK : 0 ≤ K)
    (hm : ∀ e, |periodicCoefficient (PeriodicYee.edgeAverage Concrete.material) e| ≤ K) :
    ∃ L : ℕ, 8 ≤ L ∧ ∃ S₀ : LocalOperator (N := (edges (cube L)).card),
      ∃ κ R ρ : ℝ, 0 < κ ∧ 0 ≤ R ∧ 0 < ρ ∧ IsSelfAdjoint S₀ ∧
      (∀ ξ : ℝ, 0 < ξ → ξ < ρ →
        ‖S₀ - compression (edgeEmbedding (cube L)) (coordinateWeight (cube L))
            (PeriodicYee.edgeAverage Concrete.material) K hK hm (pointEnergy - ξ) -
          (κ * Real.sqrt ξ) • rankOne ℂ
            ((localSource (edgeEmbedding (cube L)) (coordinateWeight (cube L))
              (angularTorusPoint conventionalPointMomentum) 0).adjoint S.eigenvector)
            ((localSource (edgeEmbedding (cube L)) (coordinateWeight (cube L))
              (angularTorusPoint conventionalPointMomentum) 0).adjoint S.eigenvector)‖ ≤ R * ξ) ∧
      Tendsto (fun ξ => compression (edgeEmbedding (cube L)) (coordinateWeight (cube L))
        (PeriodicYee.edgeAverage Concrete.material) K hK hm (pointEnergy - ξ))
        (𝓝[>] 0) (𝓝 S₀) ∧
      (let w := realCoordinatePart (coherentCoordinates L S.eigenvector
          (fun n => UnitAddTorus.mFourier n (angularTorusPoint conventionalPointMomentum)));
        threshold * ‖w‖ ^ 2 < inner ℝ w (realPartOperator S₀ w)) := by
  obtain ⟨B, φ, r₀, C, hr₀, hC, hrB, hcont, hφ⟩ :=
    exists_conventional_coherent_chart S hu hlower heven hreal halg
  obtain ⟨δ, g, hδ, hg, hgap⟩ := exists_physical_negative_gap S
  let dmax := ‖B.quadraticRoot.toContinuousLinearMap‖ ^ 2 +
    B.dispersionRemainder * B.radius ^ 2 + 1
  have hdmax : 0 < dmax := by
    dsimp [dmax]
    have hD := B.dispersionRemainder_nonneg
    positivity
  let r := min r₀ (min (1 / 64) (1 / (64 * (1 + C))))
  have hr : 0 < r := by dsimp [r]; positivity
  have hrr₀ : r ≤ r₀ := min_le_left _ _
  have hrsmall : r ≤ 1 / 64 := (min_le_right _ _).trans (min_le_left _ _)
  have hrC : r ≤ 1 / (64 * (1 + C)) := (min_le_right _ _).trans (min_le_right _ _)
  have ha : 0 < r / (80 * dmax) := by positivity
  obtain ⟨n, hn⟩ := exists_nat_gt ((threshold + 1 / g) / (r / (80 * dmax)))
  let L := max 8 n
  have hL : 8 ≤ L := Nat.le_max_left _ _
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hlarge : threshold < (r / (80 * dmax)) * (L : ℝ) ^ 2 - 1 / g := by
    have hLn : (n : ℝ) ≤ L := by exact_mod_cast (Nat.le_max_right 8 n)
    have hh := (div_lt_iff₀ ha).mp (hn.trans_le hLn)
    have hs : (L : ℝ) ≤ (L : ℝ) ^ 2 := by nlinarith
    have hm := mul_le_mul_of_nonneg_left hs ha.le
    nlinarith
  have hsub : Metric.ball (0 : Momentum) (r / L) ⊆ Metric.ball 0 r₀ :=
    Metric.ball_subset_ball ((div_le_self hr.le hL1).trans hrr₀)
  have hsubB : Metric.ball (0 : Momentum) (r / L) ⊆ Metric.ball 0 B.radius :=
    hsub.trans (Metric.ball_subset_ball hrB)
  obtain ⟨S₀, κ, R, ρ, hκ, hR, hρ, hself, hexp, hlim⟩ :=
    conventional_compression_sqrt_limit (edgeEmbedding (cube L)) (coordinateWeight (cube L))
      S hlower heven hreal halg haug K hK hm
  refine ⟨L, hL, S₀, κ, R, ρ, hκ, hR, hρ, hself, hexp, hlim, ?_⟩
  let ξ := fun n : ℕ => (δ / 2) * (1 / ((n : ℝ) + 1))
  have hξ (n : ℕ) : 0 < ξ n := by dsimp [ξ]; positivity
  have hξδ (n : ℕ) : ξ n < δ := by
    have hfrac : 1 / ((n : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity)).mpr (le_add_of_nonneg_left (Nat.cast_nonneg n))
    have hh := mul_le_mul_of_nonneg_left hfrac (half_pos hδ).le
    dsimp [ξ]
    linarith
  have hξlim : Tendsto ξ atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (δ / 2)
  have hξwithin : Tendsto ξ atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hξlim, Eventually.of_forall hξ⟩
  have hS := realPartOperator_tendsto _ S₀ (hlim.comp hξwithin)
  have heig : ∀ q : Momentum, q ∈ Metric.ball 0 (r / L) →
      Matrix.toEuclideanCLM (n := Edge20) (𝕜 := ℂ)
        (torusElectric (PeriodicYee.edgeAverage Concrete.material)
          (angularTorusPoint conventionalPointMomentum + Bloch.momentumTorus q)) (φ q) =
            (pointEnergy + B.dispersion q : ℂ) • φ q := by
    intro q hq
    have he := (hφ q (hsub hq)).2.2
    rw [fiber, momentumTorus_eq_angular,
      show angularTorusPoint q.ofLp = Bloch.momentumTorus q.ofLp from rfl,
      Complex.ofReal_add] at he
    exact he
  exact coherent_cube_high_rayleigh L hL S.eigenvector hu hureal
    (angularTorusPoint conventionalPointMomentum) conventional_point_center_trim
    (PeriodicYee.edgeAverage Concrete.material) K hK hm pointEnergy g threshold hg
    φ B.dispersion hr B.coercivity_pos hdmax hC.le hrsmall hrC hlarge
    (hcont.mono hsub) (fun q hq => (hφ q (hsub hq)).1)
    (fun q hq => (hφ q (hsub hq)).2.1)
    heig
    B.dispersion_measurable (fun q hq => chart_dispersion_nonneg B q (hsubB hq))
    (fun q hq hq0 => B.dispersion_coercive q (hsubB hq) hq0)
    (fun q hq => B.dispersion_upper q (hsubB hq))
    ξ hξ hξlim (fun n => (hgap (ξ n) (hξ n) (hξδ n)).1)
    (fun n => (hgap (ξ n) (hξ n) (hξδ n)).2) (realPartOperator S₀) hS

end
end Maxwell.Defect.ScalarDefect
