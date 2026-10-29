import Maxwell.Defect.PhysicalRegularConstruction

/-! Resolvent norm budgets from the actual local pole and far-region fibers.
No inverse norm estimate is assumed as an input to the pole estimate. -/
namespace Maxwell.Defect.PhysicalLimit

open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Spectral.Bloch
open Maxwell.Spectral.AnalyticEigenbranch Maxwell.Spectral.BlochResolvent
open Maxwell.Spectral.BlochSpectrum Maxwell.Green Maxwell.Green.SourceProfile
open Maxwell.Green.PhysicalAnalytic
open MeasureTheory Set Filter
open scoped Topology Matrix.Norms.L2Operator

noncomputable section
set_option maxHeartbeats 1000000

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The actual pole formula bounds the inverse by the projector norm divided
by the energy distance, plus the bounded regular part. -/
theorem inverse_norm_le_pole (T P : FiberOperator) (edge d ξ CP CR : ℝ)
    (hd : 0 ≤ d) (hξ : 0 < ξ)
    (hPP : P * P = P) (hTP : T * P = ((edge + d : ℝ) : ℂ) • P)
    (hPT : P * T = ((edge + d : ℝ) : ℂ) • P)
    (hi : (T - ((edge - ξ : ℝ) : ℂ) • 1 + P).IsInvertible)
    (hP : ‖P‖ ≤ CP)
    (hR : ‖regularResolvent T P ((edge - ξ : ℝ) : ℂ)‖ ≤ CR) :
    (T - ((edge - ξ : ℝ) : ℂ) • 1).IsInvertible ∧
      ‖(T - ((edge - ξ : ℝ) : ℂ) • 1).inverse‖ ≤ CP / ξ + CR := by
  have hpos : 0 < d + ξ := add_pos_of_nonneg_of_pos hd hξ
  have he : ((edge + d : ℝ) : ℂ) - ((edge - ξ : ℝ) : ℂ) = ((d + ξ : ℝ) : ℂ) := by
    push_cast
    ring
  obtain ⟨hI, hEq⟩ := inverse_eq_pole_add_regular T P
    ((edge + d : ℝ) : ℂ) ((edge - ξ : ℝ) : ℂ) hPP hTP hPT hi
    (by rw [he]; exact Complex.ofReal_ne_zero.mpr hpos.ne')
  refine ⟨hI, ?_⟩
  rw [hEq, he]
  calc
    _ ≤ ‖((d + ξ : ℝ) : ℂ)⁻¹ • P‖ +
        ‖regularResolvent T P ((edge - ξ : ℝ) : ℂ)‖ := norm_add_le _ _
    _ = (d + ξ)⁻¹ * ‖P‖ + ‖regularResolvent T P ((edge - ξ : ℝ) : ℂ)‖ := by
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    _ ≤ ξ⁻¹ * CP + CR := add_le_add
      (mul_le_mul (inv_anti₀ hξ (by linarith)) hP (norm_nonneg _) (by positivity)) hR
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

/-- Unitary Bloch transport and the C*-norm of the continuous matrix symbol
transfer a uniform finite-fiber inverse bound to the infinite Yee operator. -/
theorem electric_inverse_norm_le_of_fibers (m : Edge20 → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hm : ∀ e, |periodicCoefficient m e| ≤ K)
    (E B : ℝ) (hB : 0 ≤ B)
    (hE : ∀ t : Torus, E ∉ spectrum ℝ (torusElectric m t))
    (hbound : ∀ t : Torus,
      ‖(Matrix.toEuclideanCLM (n := Edge20) (𝕜 := ℂ) (torusElectric m t) -
        (E : ℂ) • 1).inverse‖ ≤ B) :
    ‖Ring.inverse (electricOperator (periodicCoefficient m) K hK hm - (E : ℂ) • 1)‖ ≤ B := by
  rw [← StarAlgEquiv.norm_map transform.conjStarAlgEquiv,
    transform_electric_inverse m K hK hm E hE]
  apply (NonUnitalStarAlgHom.norm_apply_le (matrixMultiplierHom volume)
    (inverseElectricSymbol m E)).trans
  apply (ContinuousMap.norm_le _ hB).mpr
  intro t
  rw [inverseElectricSymbol_apply m E hE]
  rw [← Matrix.l2_opNorm_toEuclideanCLM, matrixInverse_operator]
  simpa only [map_sub, map_smul, map_one] using hbound t

theorem electric_shift_isUnit_of_fibers (m : Edge20 → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hm : ∀ e, |periodicCoefficient m e| ≤ K)
    (E : ℝ) (hE : ∀ t : Torus, E ∉ spectrum ℝ (torusElectric m t)) :
    IsUnit (electricOperator (periodicCoefficient m) K hK hm - (E : ℂ) • 1) := by
  have hz : E ∉ spectrum ℝ (electricOperator (periodicCoefficient m) K hK hm) := by
    rw [electricOperator_spectrum_torus]
    simpa only [Set.mem_iUnion, not_exists] using hE
  have h := (spectrum.notMem_iff.mp hz).neg
  have he : E • (1 : Field →L[ℂ] Field) = (E : ℂ) • (1 : Field →L[ℂ] Field) := by
    ext x e
    exact Complex.real_smul
  simpa only [neg_sub, Algebra.algebraMap_eq_smul_one, he] using h

theorem torus_gap_of_inverse (m : Edge20 → ℝ) (E : ℝ)
    (hI : ∀ t : Torus, (Matrix.toEuclideanCLM (n := Edge20) (𝕜 := ℂ)
      (torusElectric m t) - (E : ℂ) • 1).IsInvertible) :
    ∀ t : Torus, E ∉ spectrum ℝ (torusElectric m t) := by
  intro t
  have hi : (Matrix.toEuclideanCLM (n := Edge20) (𝕜 := ℂ)
      (torusElectric m t - (E : ℂ) • 1)).IsInvertible := by
    simpa only [map_sub, map_smul, map_one] using hI t
  obtain ⟨e, heq⟩ := hi
  have hu : IsUnit (Matrix.toEuclideanCLM (n := Edge20) (𝕜 := ℂ)
      (torusElectric m t - (E : ℂ) • 1)) := heq ▸ e.toUnit.isUnit
  have hm : IsUnit (torusElectric m t - (E : ℂ) • 1) := by
    have h := hu.map (Matrix.toEuclideanCLM (n := Edge20) (𝕜 := ℂ)).symm.toMonoidHom
    change IsUnit ((Matrix.toEuclideanCLM (n := Edge20) (𝕜 := ℂ)).symm
      (Matrix.toEuclideanCLM (n := Edge20) (𝕜 := ℂ) (torusElectric m t - (E : ℂ) • 1))) at h
    simpa only [StarAlgEquiv.symm_apply_apply] using h
  apply spectrum.notMem_iff.mpr
  have hs : E • (1 : Matrix Edge20 Edge20 ℂ) = (E : ℂ) • (1 : Matrix Edge20 Edge20 ℂ) := by
    ext i j
    exact Complex.real_smul
  simpa only [neg_sub, Algebra.algebraMap_eq_smul_one, hs] using hm.neg

theorem chart_dispersion_nonneg {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (C : LocalBandChart F) (q : Momentum) (hq : q ∈ Metric.ball 0 C.radius) :
    0 ≤ C.dispersion q := by
  by_cases hz : q = 0
  · subst q
    have h := C.dispersion_quartic 0 hq
    have he : C.dispersion 0 = 0 := by simpa using h
    exact he.ge
  · exact (mul_nonneg C.coercivity_pos.le (sq_nonneg ‖q‖)).trans
      (C.dispersion_coercive q hq hz)

/-- One local pole region and its full far complement give a common inverse
budget; the energy radius is restricted to one only to absorb bounded terms. -/
theorem inverse_norm_le_local_far (T P : Momentum → FiberOperator) (d : Momentum → ℝ)
    (Ω : Set Momentum) (edge radius ξ CP CR CF : ℝ)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hCP : 0 ≤ CP) (hCR : 0 ≤ CR) (hCF : 0 ≤ CF)
    (hloc : ∀ q ∈ Metric.ball 0 radius, 0 ≤ d q ∧
      P q * P q = P q ∧ T q * P q = ((edge + d q : ℝ) : ℂ) • P q ∧
      P q * T q = ((edge + d q : ℝ) : ℂ) • P q ∧ ‖P q‖ ≤ CP)
    (hreg : ∀ q ∈ Metric.ball 0 radius,
      (T q - ((edge - ξ : ℝ) : ℂ) • 1 + P q).IsInvertible ∧
      ‖regularResolvent (T q) (P q) ((edge - ξ : ℝ) : ℂ)‖ ≤ CR)
    (hfar : ∀ q ∈ Ω \ Metric.ball 0 radius,
      (T q - ((edge - ξ : ℝ) : ℂ) • 1).IsInvertible ∧
      ‖(T q - ((edge - ξ : ℝ) : ℂ) • 1).inverse‖ ≤ CF) :
    ∀ q ∈ Ω, (T q - ((edge - ξ : ℝ) : ℂ) • 1).IsInvertible ∧
      ‖(T q - ((edge - ξ : ℝ) : ℂ) • 1).inverse‖ ≤ (CP + CR + CF) / ξ := by
  intro q hq
  by_cases hball : q ∈ Metric.ball 0 radius
  · obtain ⟨hd, hPP, hTP, hPT, hP⟩ := hloc q hball
    obtain ⟨hi, hR⟩ := hreg q hball
    obtain ⟨hI, hnorm⟩ := inverse_norm_le_pole (T q) (P q) edge (d q) ξ CP CR
      hd hξ hPP hTP hPT hi hP hR
    refine ⟨hI, hnorm.trans ?_⟩
    apply (le_div_iff₀ hξ).mpr
    have he : CP / ξ * ξ = CP := div_mul_cancel₀ CP hξ.ne'
    have hRξ : CR * ξ ≤ CR := mul_le_of_le_one_right hCR hξ1
    nlinarith
  · obtain ⟨hi, hn⟩ := hfar q ⟨hq, hball⟩
    refine ⟨hi, ?_⟩
    apply (le_div_iff₀ hξ).mpr
    calc
      _ ≤ CF * ξ := mul_le_mul_of_nonneg_right hn hξ.le
      _ ≤ CF := mul_le_of_le_one_right hCF hξ1
      _ ≤ CP + CR + CF := by linarith

theorem torus_inverse_norm_le_of_angular_cube (material : Cell20 → ℝ)
    (θ : RealTorusCoordinates) (E B : ℝ)
    (hbound : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi),
      ‖(shiftedOperator material E (complexifyCoordinates θ + complexifyCoordinates q)).inverse‖ ≤ B) :
    ∀ t : Torus, ‖(Matrix.toEuclideanCLM (n := Edge20) (𝕜 := ℂ)
      (torusElectric (PeriodicYee.edgeAverage material) t) - (E : ℂ) • 1).inverse‖ ≤ B := by
  intro t
  obtain ⟨q, hq, ht⟩ := exists_angular_representative (t - angularTorusPoint θ)
  have he : angularTorusPoint (θ + q) = t := by
    rw [angularTorusPoint_add, ht, add_sub_cancel]
  have h := hbound q hq
  have hadd : complexifyCoordinates θ + complexifyCoordinates q = complexifyCoordinates (θ + q) :=
    (map_add complexifyCLM θ q).symm
  rw [hadd, shiftedOperator_real, he] at h
  simpa only [map_sub, map_smul, map_one] using h

/-- Local projection algebra, nonnegative dispersion, and full real far
exclusion produce a uniform inverse bound for every finite physical fiber. -/
theorem exists_fiber_inverse_bound (material : Cell20 → ℝ) (edge : ℝ)
    (θ : RealTorusCoordinates) (P : Momentum → FiberOperator) (d : Momentum → ℝ)
    (hP : ContinuousAt P 0) (hd : ∀ᶠ q in 𝓝 (0 : Momentum), 0 ≤ d q)
    (hAlg : ∀ᶠ q in 𝓝 (0 : Momentum), P q * P q = P q ∧
      fiber (PeriodicYee.edgeAverage material) (angularTorusPoint θ) q * P q =
        ((edge + d q : ℝ) : ℂ) • P q ∧
      P q * fiber (PeriodicYee.edgeAverage material) (angularTorusPoint θ) q =
        ((edge + d q : ℝ) : ℂ) • P q)
    (hi : (fiber (PeriodicYee.edgeAverage material) (angularTorusPoint θ) 0 -
      (edge : ℂ) • 1 + P 0).IsInvertible)
    (hexclude : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 →
      (shiftedOperator material edge (complexifyCoordinates θ + complexifyCoordinates q)).IsInvertible) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ ξ : ℝ, 0 < ξ → ξ < δ →
      ∀ q ∈ closedPhysicalCell,
        (fiber (PeriodicYee.edgeAverage material) (angularTorusPoint θ) q -
          ((edge - ξ : ℝ) : ℂ) • 1).IsInvertible ∧
        ‖(fiber (PeriodicYee.edgeAverage material) (angularTorusPoint θ) q -
          ((edge - ξ : ℝ) : ℂ) • 1).inverse‖ ≤ C / ξ := by
  let T := fiber (PeriodicYee.edgeAverage material) (angularTorusPoint θ)
  let CP := ‖P 0‖ + 1
  have hCP : 0 < CP := by dsimp [CP]; positivity
  have hPb : ∀ᶠ q in 𝓝 (0 : Momentum), ‖P q‖ < CP :=
    hP.norm.eventually (gt_mem_nhds (by simp [CP]))
  obtain ⟨r0, hr0, h0⟩ := Metric.eventually_nhds_iff_ball.mp ((hd.and hAlg).and hPb)
  obtain ⟨rL, CR, hrL, hCR, hreg⟩ := exists_local_regular_bounds T P edge
    (fiber_continuous material θ).continuousAt hP hi
  let radius := min r0 rL
  have hradius : 0 < radius := lt_min hr0 hrL
  obtain ⟨rF, CF, hrF, hCF, hfar⟩ :=
    exists_far_inverse_bounds material edge θ radius hradius hexclude
  refine ⟨min (min rL rF) 1, CP + CR + CF, by positivity, by positivity, ?_⟩
  intro ξ hξ hξδ
  have hξL : |ξ| < rL := by
    rw [abs_of_pos hξ]
    exact (lt_min_iff.mp (lt_min_iff.mp hξδ).1).1
  have hξF : |ξ| < rF := by
    rw [abs_of_pos hξ]
    exact (lt_min_iff.mp (lt_min_iff.mp hξδ).1).2
  apply inverse_norm_le_local_far T P d closedPhysicalCell edge radius ξ CP CR CF
    hξ (lt_min_iff.mp hξδ).2.le hCP.le hCR.le hCF.le
  · intro q hq
    have hq0 : q ∈ Metric.ball 0 r0 := Metric.mem_ball.mpr
      ((Metric.mem_ball.mp hq).trans_le (min_le_left _ _))
    obtain ⟨⟨hdq, hPP, hTP, hPT⟩, hPq⟩ := h0 q hq0
    exact ⟨hdq, hPP, hTP, hPT, hPq.le⟩
  · intro q hq
    have hqL : ‖q‖ < rL := by
      have hh := (Metric.mem_ball.mp hq).trans_le (min_le_right r0 rL)
      simpa only [dist_zero_right] using hh
    exact hreg q hqL ξ hξL
  · exact hfar ξ hξF

/-- A fixed positive rational constant controls the genuine infinite
resolvent throughout a punctured one-sided neighborhood of the band edge. -/
theorem exists_electric_inverse_bound (material : Cell20 → ℝ) (edge : ℝ)
    (θ : RealTorusCoordinates) (P : Momentum → FiberOperator) (d : Momentum → ℝ)
    (hP : ContinuousAt P 0) (hd : ∀ᶠ q in 𝓝 (0 : Momentum), 0 ≤ d q)
    (hAlg : ∀ᶠ q in 𝓝 (0 : Momentum), P q * P q = P q ∧
      fiber (PeriodicYee.edgeAverage material) (angularTorusPoint θ) q * P q =
        ((edge + d q : ℝ) : ℂ) • P q ∧
      P q * fiber (PeriodicYee.edgeAverage material) (angularTorusPoint θ) q =
        ((edge + d q : ℝ) : ℂ) • P q)
    (hi : (fiber (PeriodicYee.edgeAverage material) (angularTorusPoint θ) 0 -
      (edge : ℂ) • 1 + P 0).IsInvertible)
    (hexclude : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 →
      (shiftedOperator material edge (complexifyCoordinates θ + complexifyCoordinates q)).IsInvertible) :
    ∃ δ : ℝ, ∃ C : ℚ, 0 < δ ∧ 0 < C ∧
      ∀ z : ℝ, 0 < edge - z → edge - z < δ →
      ∀ (K : ℝ) (hK : 0 ≤ K)
        (hm : ∀ e, |periodicCoefficient (PeriodicYee.edgeAverage material) e| ≤ K),
        IsUnit (electricOperator (periodicCoefficient (PeriodicYee.edgeAverage material))
          K hK hm - (z : ℂ) • 1) ∧
        ‖Ring.inverse (electricOperator (periodicCoefficient (PeriodicYee.edgeAverage material))
          K hK hm - (z : ℂ) • 1)‖ ≤ (C : ℝ) / (edge - z) := by
  obtain ⟨δ, C, hδ, hC, hf⟩ :=
    exists_fiber_inverse_bound material edge θ P d hP hd hAlg hi hexclude
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have hn0 : (0 : ℚ) < n := by exact_mod_cast (hC.trans hn)
  refine ⟨δ, (n : ℚ), hδ, hn0, ?_⟩
  intro z hz hzδ K hK hm
  have he : edge - (edge - z) = z := by ring
  have hc : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi),
      (shiftedOperator material z (complexifyCoordinates θ + complexifyCoordinates q)).IsInvertible ∧
      ‖(shiftedOperator material z (complexifyCoordinates θ + complexifyCoordinates q)).inverse‖ ≤
        C / (edge - z) := by
    intro q hq
    have h := hf (edge - z) hz hzδ (WithLp.toLp 2 q) ⟨q, hq, rfl⟩
    have hq' : momentumComplex (WithLp.toLp 2 q) = complexifyCoordinates q := by
      ext j
      rfl
    rw [fiber_conventional, he, hq'] at h
    exact h
  have hE := real_torus_gap_of_centered_inverse material z θ (fun q hq => (hc q hq).1)
  refine ⟨electric_shift_isUnit_of_fibers _ K hK hm z hE, ?_⟩
  have hb := electric_inverse_norm_le_of_fibers (PeriodicYee.edgeAverage material) K hK hm
    z (C / (edge - z)) (div_nonneg hC.le hz.le) hE
    (torus_inverse_norm_le_of_angular_cube material θ z (C / (edge - z))
      (fun q hq => (hc q hq).2))
  exact hb.trans (div_le_div_of_nonneg_right (by exact_mod_cast hn.le) hz.le)

/-- A certified lower enclosure of the edge gives a rational energy-distance
budget usable by the finite inverse certificate. -/
theorem inverse_bound_of_edge_lower (H : Field →L[ℂ] Field) (edge : ℝ)
    (C lower z : ℚ) (hC : 0 ≤ C) (hz : z < lower) (hlower : (lower : ℝ) ≤ edge)
    (hbound : ‖Ring.inverse (H - (z : ℂ) • 1)‖ ≤ (C : ℝ) / (edge - z)) :
    ‖Ring.inverse (H - (z : ℂ) • 1)‖ ≤ ((C / (lower - z) : ℚ) : ℝ) := by
  have hdist : (0 : ℝ) < (lower : ℝ) - z := by exact_mod_cast sub_pos.mpr hz
  have hC' : (0 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC
  rw [Rat.cast_div, Rat.cast_sub]
  exact hbound.trans (div_le_div_of_nonneg_left hC' hdist (by linarith))

end
end Maxwell.Defect.PhysicalLimit
