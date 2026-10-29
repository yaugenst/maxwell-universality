import Maxwell.Defect.PhysicalLocalChart

/-! Uniform local and far inverse bounds for the actual physical edge
compression, obtained from openness and compactness. -/
namespace Maxwell.Defect.PhysicalLimit
open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Spectral.Bloch
open Maxwell.Spectral.AnalyticEigenbranch
open Maxwell.Green Maxwell.Green.SourceProfile Maxwell.Green.PhysicalAnalytic
open Filter Set MeasureTheory
open scoped Topology
noncomputable section
variable {N : ℕ}
set_option maxHeartbeats 1000000

theorem fiber_conventional (material : Cell20 → ℝ) (θ : RealTorusCoordinates)
    (q : Momentum) :
    fiber (PeriodicYee.edgeAverage material) (angularTorusPoint θ) q =
      ConventionalAnalytic.operator material (complexifyCoordinates θ + momentumComplex q) := by
  rw [← realMomentum_add]
  change _ = ConventionalAnalytic.operator material (ConventionalAnalytic.realMomentum (θ + q.ofLp))
  rw [ConventionalAnalytic.operator_real]
  simp only [fiber, momentumTorus_eq_angular, ← angularTorusPoint_add]
  change Matrix.toEuclideanCLM (n := Edge20) (𝕜 := ℂ)
    (torusElectric (PeriodicYee.edgeAverage material) (Maxwell.Spectral.Bloch.momentumTorus (θ + q.ofLp))) = _
  rw [torusElectric_eq_periodic]

theorem fiber_continuous (material : Cell20 → ℝ) (θ : RealTorusCoordinates) :
    Continuous (fiber (PeriodicYee.edgeAverage material) (angularTorusPoint θ)) := by
  change Continuous (fun q => fiber (PeriodicYee.edgeAverage material) (angularTorusPoint θ) q)
  simp_rw [fiber_conventional]
  have hc : Continuous (ConventionalAnalytic.operator material) :=
    continuous_iff_continuousAt.mpr fun z =>
      (ConventionalAnalytic.operator_analyticAt material z).continuousAt
  exact hc.comp (continuous_const.add momentumComplexCLM.continuous)

theorem localSource_continuous (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (θ : RealTorusCoordinates) :
    Continuous (localSource edges W (angularTorusPoint θ)) := by
  change Continuous (fun q => localSource edges W (angularTorusPoint θ) q)
  simp_rw [localSource_angular]
  have hc : Continuous (sourceRight edges W) :=
    continuous_iff_continuousAt.mpr fun z => (sourceRight_analyticAt edges W z).continuousAt
  exact hc.comp (continuous_const.add momentumComplexCLM.continuous)

private theorem compression_continuous {U H : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    Continuous (sourceCompression : (U →L[ℂ] H) → (H →L[ℂ] H) →L[ℂ] (U →L[ℂ] U)) := by
  have hl : Continuous (fun F : U →L[ℂ] H =>
      ContinuousLinearMap.compL ℂ U H U (ContinuousLinearMap.adjoint F)) :=
    (ContinuousLinearMap.compL ℂ U H U).continuous.comp ContinuousLinearMap.adjoint.continuous
  have hr : Continuous (fun F : U →L[ℂ] H =>
      (ContinuousLinearMap.compL ℂ U H H).flip F) :=
    (ContinuousLinearMap.compL ℂ U H H).flip.continuous
  exact hl.clm_comp hr

theorem sourceMap_continuous (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (θ : RealTorusCoordinates) :
    Continuous (sourceMap edges W (angularTorusPoint θ)) :=
  (ContinuousLinearMap.continuous_restrictScalars ℝ).comp
    (compression_continuous.comp (localSource_continuous edges W θ))

theorem regularResolvent_continuousAt
    {Z H : Type*} [NormedAddCommGroup Z]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (T P : Z → H →L[ℂ] H) (edge : ℝ) (q : Z) (ξ : ℝ)
    (hT : ContinuousAt T q) (hP : ContinuousAt P q)
    (hi : (T q - ((edge - ξ : ℝ) : ℂ) • 1 + P q).IsInvertible) :
    ContinuousAt (fun z : Z × ℝ =>
      regularResolvent (T z.1) (P z.1) ((edge - z.2 : ℝ) : ℂ)) (q, ξ) := by
  have hA : ContinuousAt (fun z : Z × ℝ =>
      T z.1 - ((edge - z.2 : ℝ) : ℂ) • 1 + P z.1) (q, ξ) :=
    ((hT.comp (f := fun z : Z × ℝ => z.1) continuousAt_fst).sub
      ((Complex.continuous_ofReal.continuousAt.comp
        (continuousAt_const.sub continuousAt_snd)).smul continuousAt_const)).add
      (hP.comp (f := fun z : Z × ℝ => z.1) continuousAt_fst)
  have hAi : ContinuousAt (fun z : Z × ℝ =>
      (T z.1 - ((edge - z.2 : ℝ) : ℂ) • 1 + P z.1).inverse) (q, ξ) := by
    apply ContinuousAt.comp (f := fun z : Z × ℝ =>
      T z.1 - ((edge - z.2 : ℝ) : ℂ) • 1 + P z.1)
      (g := ContinuousLinearMap.inverse (R := ℂ) (M := H))
    · exact (ComplexContourGap.analyticAt_inverse_operator hi).continuousAt
    · exact hA
  unfold regularResolvent
  exact ((continuousAt_const.sub (hP.comp (f := fun z : Z × ℝ => z.1) continuousAt_fst)).mul
    hAi).mul
      (continuousAt_const.sub (hP.comp (f := fun z : Z × ℝ => z.1) continuousAt_fst))

/-- The local inverse and its norm bound follow from the actual augmented
inverse at the edge; the energy and momentum radii are simultaneous. -/
theorem exists_local_regular_bounds
    {Z H : Type*} [NormedAddCommGroup Z]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (T P : Z → H →L[ℂ] H) (edge : ℝ)
    (hT : ContinuousAt T 0) (hP : ContinuousAt P 0)
    (hi : (T 0 - (edge : ℂ) • 1 + P 0).IsInvertible) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ ∀ q, ‖q‖ < r → ∀ ξ : ℝ, |ξ| < r →
      (T q - ((edge - ξ : ℝ) : ℂ) • 1 + P q).IsInvertible ∧
      ‖regularResolvent (T q) (P q) ((edge - ξ : ℝ) : ℂ)‖ ≤ C := by
  have hA : ContinuousAt (fun z : Z × ℝ =>
      T z.1 - ((edge - z.2 : ℝ) : ℂ) • 1 + P z.1) (0, 0) :=
    ((hT.comp (f := fun z : Z × ℝ => z.1) continuousAt_fst).sub
      ((Complex.continuous_ofReal.continuousAt.comp
        (continuousAt_const.sub continuousAt_snd)).smul continuousAt_const)).add
      (hP.comp (f := fun z : Z × ℝ => z.1) continuousAt_fst)
  have hinv : ∀ᶠ z : Z × ℝ in 𝓝 (0, 0),
      (T z.1 - ((edge - z.2 : ℝ) : ℂ) • 1 + P z.1).IsInvertible :=
    hA.tendsto.eventually (by simpa only [sub_zero] using hi.eventually_nhds)
  have hR := regularResolvent_continuousAt T P edge 0 0 hT hP
    (by simpa only [sub_zero] using hi)
  let C := ‖regularResolvent (T 0) (P 0) edge‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hn : ∀ᶠ z : Z × ℝ in 𝓝 (0, 0),
      ‖regularResolvent (T z.1) (P z.1) ((edge - z.2 : ℝ) : ℂ)‖ < C :=
    hR.norm.eventually (gt_mem_nhds (by simp [C]))
  obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff_ball.mp (hinv.and hn)
  refine ⟨r, C, hr, hC, fun q hq ξ hξ => ?_⟩
  have hp : (q, ξ) ∈ Metric.ball (0, 0) r := by
    simpa only [Metric.mem_ball, Prod.dist_eq, dist_zero_right, Real.norm_eq_abs,
      max_lt_iff] using And.intro hq hξ
  exact ⟨(h _ hp).1, (h _ hp).2.le⟩

def closedPhysicalCell : Set Momentum :=
  (WithLp.toLp 2) '' torusCube (-Real.pi) (2 * Real.pi)

theorem closedPhysicalCell_compact : IsCompact closedPhysicalCell :=
  (isCompact_torusCube _ _).image (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ))

theorem physicalCell_subset_closed : TorusChart.physicalCell ⊆ closedPhysicalCell := by
  intro q hq
  refine ⟨WithLp.ofLp q, ?_, rfl⟩
  intro j
  obtain ⟨hl, hu⟩ := hq j
  exact ⟨hl.le, by linarith⟩

/-- Removing any positive local ball gives a compact region of actual
invertible edge fibers and one uniform two-sided energy neighborhood. -/
theorem exists_far_inverse_bounds (material : Cell20 → ℝ) (edge : ℝ)
    (θ : RealTorusCoordinates) (radius : ℝ) (hr : 0 < radius)
    (hexclude : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 →
      (shiftedOperator material edge (complexifyCoordinates θ + complexifyCoordinates q)).IsInvertible) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ ∀ ξ : ℝ, |ξ| < r →
      ∀ q ∈ closedPhysicalCell \ Metric.ball 0 radius,
        (fiber (PeriodicYee.edgeAverage material) (angularTorusPoint θ) q -
          ((edge - ξ : ℝ) : ℂ) • 1).IsInvertible ∧
        ‖(fiber (PeriodicYee.edgeAverage material) (angularTorusPoint θ) q -
          ((edge - ξ : ℝ) : ℂ) • 1).inverse‖ ≤ C := by
  let T := fiber (PeriodicYee.edgeAverage material) (angularTorusPoint θ)
  let F := fun z : ℝ × Momentum => T z.2 - ((edge - z.1 : ℝ) : ℂ) • 1
  have hc : Continuous F :=
    ((fiber_continuous material θ).comp continuous_snd).sub
      ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_fst)).smul continuous_const)
  have hi : ∀ q ∈ closedPhysicalCell \ Metric.ball 0 radius, (F (0, q)).IsInvertible := by
    intro q hq
    obtain ⟨v, hv, rfl⟩ := hq.1
    have hv0 : v ≠ 0 := by
      intro he
      subst v
      exact hq.2 (by simpa using Metric.mem_ball_self (x := (0 : Momentum)) hr)
    have hh := hexclude v hv hv0
    change (T (WithLp.toLp 2 v) - ((edge - 0 : ℝ) : ℂ) • 1).IsInvertible
    rw [sub_zero, show T (WithLp.toLp 2 v) =
      ConventionalAnalytic.operator material (complexifyCoordinates θ + complexifyCoordinates v) from
        fiber_conventional material θ (WithLp.toLp 2 v)]
    exact hh
  obtain ⟨r, C, hr, hC, h⟩ := ComplexContourGap.compact_inverse_neighborhood
    (closedPhysicalCell \ Metric.ball 0 radius) (closedPhysicalCell_compact.diff Metric.isOpen_ball)
    F (fun _ _ => hc.continuousAt) hi
  exact ⟨r, C, hr, hC, fun ξ hξ => h ξ (by simpa only [Real.norm_eq_abs] using hξ)⟩

end
end Maxwell.Defect.PhysicalLimit
