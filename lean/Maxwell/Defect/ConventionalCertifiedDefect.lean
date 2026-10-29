import Maxwell.Defect.ConventionalCubeRayleigh
import Maxwell.Defect.ConventionalSourceEnclosure
import Maxwell.Defect.CertifiedScalarSelection
import Maxwell.Defect.PhysicalModeRefinement
import Maxwell.Green.PhysicalSpacing

/-! Finite certified selection of the scalar defect and its physical Green
spacing family from one actual conventional spectral edge. -/
namespace Maxwell.Defect.ScalarDefect

open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Spectral.Bloch
open Maxwell.Green Maxwell.Green.SourceProfile Maxwell.Green.PhysicalAnalytic
open Maxwell.Green.PhysicalCompression Maxwell.Realization
open Maxwell.Certificate Maxwell.Certificate.PointWitness
open Maxwell.Defect.PhysicalLimit
open Filter Set MeasureTheory InnerProductSpace Module.End
open scoped Topology

noncomputable section
set_option maxHeartbeats 1600000

theorem conventional_coefficient_bound (e : Edge) :
    |periodicCoefficient (PeriodicYee.edgeAverage Concrete.material) e| ≤ 13 := by
  rw [← FiniteStencil.frozenEdgeCoefficientQ_binding]
  exact FiniteStencil.frozenEdgeCoefficientQ_abs e

def conventionalCubeCompression (L : ℕ) (z : ℝ) : LocalOperator (N := (edges (cube L)).card) :=
  compression (edgeEmbedding (cube L)) (coordinateWeight (cube L))
    (PeriodicYee.edgeAverage Concrete.material) 13 (by norm_num) conventional_coefficient_bound z

def conventionalCubeSource (L : ℕ) (φ : EuclideanSpace ℂ Edge20) :=
  realCoordinatePart (coherentCoordinates L φ
    (fun n => UnitAddTorus.mFourier n (angularTorusPoint conventionalPointMomentum)))

def conventionalCubePath (L : ℕ) (S₀ : LocalOperator (N := (edges (cube L)).card))
    (ξ : ℝ) :=
  if ξ = 0 then realPartOperator S₀
  else realPartOperator (conventionalCubeCompression L (pointEnergy - ξ))

@[simp] theorem conventionalCubePath_zero (L : ℕ)
    (S₀ : LocalOperator (N := (edges (cube L)).card)) :
    conventionalCubePath L S₀ 0 = realPartOperator S₀ := by
  simp only [conventionalCubePath, ite_true]

theorem conventionalCubePath_symmetric (L : ℕ)
    (S₀ : LocalOperator (N := (edges (cube L)).card)) (hS₀ : IsSelfAdjoint S₀) (ξ : ℝ) :
    (conventionalCubePath L S₀ ξ).toLinearMap.IsSymmetric := by
  unfold conventionalCubePath
  split_ifs
  · exact realPartOperator_symmetric _ hS₀
  · exact realPartOperator_symmetric _ (compression_selfAdjoint _ _ _ _ _ _ _)

theorem conventionalCubePath_binding (L : ℕ)
    (S₀ : LocalOperator (N := (edges (cube L)).card)) (z : ℚ) (hz : (z : ℝ) < pointEnergy) :
    conventionalCubePath L S₀ (pointEnergy - (z : ℝ)) =
      FiniteStencil.weightedInverseCompression (edgeEmbedding (cube L))
        FiniteStencil.frozenEdgeCoefficientQ 13 (by norm_num) FiniteStencil.frozenEdgeCoefficientQ_abs
        z (coordinateWeight (cube L)) := by
  rw [conventionalCubePath, ite_eq_right (sub_pos.mpr hz).ne', sub_sub_cancel,
    FiniteStencil.weightedInverseCompression_realPart]
  unfold conventionalCubeCompression compression FiniteStencil.operator
  have hm : (fun e => (FiniteStencil.frozenEdgeCoefficientQ e : ℝ)) =
      periodicCoefficient (PeriodicYee.edgeAverage Concrete.material) :=
    funext FiniteStencil.frozenEdgeCoefficientQ_binding
  simp only [hm, Complex.ofReal_ratCast]
  rfl

theorem conventionalCubeSource_embedding (L : ℕ) (φ : EuclideanSpace ℂ Edge20)
    (hφ : ∀ i, (φ i).im = 0) :
    (localSource (edgeEmbedding (cube L)) (coordinateWeight (cube L))
      (angularTorusPoint conventionalPointMomentum) 0).adjoint φ =
      realCoordinateEmbedding (conventionalCubeSource L φ) := by
  rw [localSource_angular,
    show momentumComplex (0 : Momentum) = 0 from map_zero momentumComplexCLM, add_zero]
  change (sourceRight (edgeEmbedding (cube L)) (coordinateWeight (cube L))
    (realMomentum conventionalPointMomentum)).adjoint φ = _
  rw [sourceRight_adjoint_coherentCoordinates]
  exact (coherentCoordinates_real_at_trim L φ hφ _ conventional_point_center_trim).symm

theorem conventionalCubePath_expansion (L : ℕ)
    (S₀ : LocalOperator (N := (edges (cube L)).card)) (φ : EuclideanSpace ℂ Edge20)
    (hφ : ∀ i, (φ i).im = 0) (κ R ρ : ℝ)
    (hexp : ∀ ξ : ℝ, 0 < ξ → ξ < ρ →
      ‖S₀ - conventionalCubeCompression L (pointEnergy - ξ) -
        (κ * Real.sqrt ξ) • rankOne ℂ
          ((localSource (edgeEmbedding (cube L)) (coordinateWeight (cube L))
            (angularTorusPoint conventionalPointMomentum) 0).adjoint φ)
          ((localSource (edgeEmbedding (cube L)) (coordinateWeight (cube L))
            (angularTorusPoint conventionalPointMomentum) 0).adjoint φ)‖ ≤ R * ξ)
    (ξ : ℝ) (hξ : 0 < ξ) (hξρ : ξ < ρ) :
    ‖conventionalCubePath L S₀ 0 - conventionalCubePath L S₀ ξ -
      (κ * Real.sqrt ξ) • rankOne ℝ (conventionalCubeSource L φ)
        (conventionalCubeSource L φ)‖ ≤ R * ξ := by
  rw [conventionalCubePath_zero, conventionalCubePath, ite_eq_right hξ.ne']
  have h := hexp ξ hξ hξρ
  rw [conventionalCubeSource_embedding L φ hφ] at h
  apply le_trans _ h
  have hn := realPartOperator_norm_le
    (S₀ - conventionalCubeCompression L (pointEnergy - ξ) -
      (κ * Real.sqrt ξ) • rankOne ℂ (realCoordinateEmbedding (conventionalCubeSource L φ))
        (realCoordinateEmbedding (conventionalCubeSource L φ)))
  change ‖realPartOperatorMap _‖ ≤ _ at hn
  simpa only [map_sub, map_smul, realPartOperatorMap_apply, realPartOperator_rankOne] using hn

theorem exists_conventionalCubeSource_sequence (L : ℕ)
    (hgap : PointClusterComplementGap) (hexclude : PointOtherSectorExclusion)
    (φ : EuclideanSpace ℂ Edge20) (hφ : φ = conventionalRealPointVector hgap hexclude) :
    ∃ (q : ℕ → Fin (edges (cube L)).card → ℚ) (β : ℕ → ℚ) (sourceBound : ℚ),
      (∀ k, ‖conventionalCubeSource L φ - rationalVector (q k)‖ ≤ (β k : ℝ)) ∧
      Tendsto (fun k => (β k : ℝ)) atTop (𝓝 0) ∧
      ‖conventionalCubeSource L φ‖ ≤ (sourceBound : ℝ) ∧ 0 < sourceBound := by
  let k := conventionalTrimCoordinates ![1, 1, 0]
  have hm : (fun r => (FiniteStencil.frozenMaterialQ r : ℝ)) = Concrete.material :=
    funext FiniteStencil.frozenMaterialQ_binding
  have hcenter : ConventionalAnalytic.trim k = conventionalPointMomentum := by
    rw [conventionalPointMomentum, pointPrimitiveMomentum, conventionalMomentum_trim]
  have hfiber : PeriodicYee.fiber (fun r => (FiniteStencil.frozenMaterialQ r : ℝ))
      (ConventionalAnalytic.trim k) = conventionalPointFiber := by
    rw [hm, hcenter]
    rfl
  have heig : Matrix.toEuclideanCLM (n := Edge20) (𝕜 := ℂ)
      (PeriodicYee.fiber (fun r => (FiniteStencil.frozenMaterialQ r : ℝ))
        (ConventionalAnalytic.trim k)) φ = (pointEnergy : ℂ) • φ := by
    rw [hfiber, hφ]
    exact conventionalRealPointVector_eigen hgap hexclude
  have hdim : Module.finrank ℂ (eigenspace
      (PeriodicYee.fiber (fun r => (FiniteStencil.frozenMaterialQ r : ℝ))
        (ConventionalAnalytic.trim k)).toEuclideanLin (pointEnergy : ℂ)) = 1 := by
    rw [hfiber]
    exact (conventionalPoint_simple_exists hgap hexclude).1
  obtain ⟨left, right, reference, hcheck, _, _, _, hq, hβ, hb, hnorm⟩ :=
    exists_conventional_coherent_sequence L FiniteStencil.frozenMaterialQ k φ pointEnergy
      (hφ ▸ conventionalRealPointVector_norm hgap hexclude)
      (hφ ▸ conventionalRealPointVector_real hgap hexclude) heig hdim
  have htorus : Bloch.momentumTorus (fun j => Real.pi * (k j : ℝ)) =
      angularTorusPoint conventionalPointMomentum := by
    change Bloch.momentumTorus (ConventionalAnalytic.trim k) = _
    rw [hcenter]
    rfl
  refine ⟨conventionalCoherentSequence L FiniteStencil.frozenMaterialQ k left right reference hcheck,
    coherentSourceError L,
    coherentSourceBound L k (conventionalVectorSequence FiniteStencil.frozenMaterialQ k left right reference hcheck),
    ?_, hβ, ?_, hb⟩
  · simpa only [conventionalCubeSource, htorus] using hq
  · simpa only [conventionalCubeSource, htorus] using hnorm

attribute [local irreducible] edges cube

set_option genSizeOf false in
set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- One accepted finite certificate, its actual scalar-defect mode, and
the spacing bounds for that same mode and operating energy. -/
structure ConventionalCertifiedCube
    (S : PhysicalSimpleEdgeData Concrete.material pointEnergy conventionalPointMomentum) where
  size : ℕ
  size_ge : 8 ≤ size
  index : ℕ
  energy_pos : 0 < (dyadicCandidate index : ℝ)
  energy_lt_edge : (dyadicCandidate index : ℝ) < pointEnergy
  energy_upper : dyadicCandidate index ≤ 957 / 100000
  normBound : ℚ
  gap : ℚ
  budget : ℚ
  normBound_pos : 0 < normBound
  gap_pos : 0 < gap
  gap_le : gap ≤ normBound
  budget_pos : 0 < budget
  operator_norm : ‖FiniteStencil.frozenOperator (dyadicCandidate index)‖ ≤ (normBound : ℝ)
  spectral_gap : ∀ x ∈ spectrum ℝ (FiniteStencil.frozenOperator (dyadicCandidate index)),
    (gap : ℝ) ≤ |x|
  operator_isUnit : IsUnit (FiniteStencil.frozenOperator (dyadicCandidate index))
  inverse_norm : ‖Ring.inverse (FiniteStencil.frozenOperator (dyadicCandidate index))‖ ≤
    1 / (gap : ℝ)
  sourceSequence : ℕ → Fin (edges (cube size)).card → ℚ
  sourceError : ℕ → ℚ
  sourceBound : ℚ
  source_enclosure : ∀ k, ‖conventionalCubeSource size S.eigenvector -
    rationalVector (sourceSequence k)‖ ≤ (sourceError k : ℝ)
  source_error_tendsto : Tendsto (fun k => (sourceError k : ℝ)) atTop (𝓝 0)
  source_bound : ‖conventionalCubeSource size S.eigenvector‖ ≤ (sourceBound : ℝ)
  sourceBound_pos : 0 < sourceBound
  stage : ℕ
  accepted : scalarModeBudgetCheck (cube size) FiniteStencil.frozenEdgeCoefficientQ
    (dyadicCandidate index) normBound gap 22 budget sourceSequence sourceError sourceBound stage = true
  eigenvalue : ℝ
  mode : EuclideanSpace ℝ (Fin (edges (cube size)).card)
  mode_unit : ‖mode‖ = 1
  mode_equation : FiniteStencil.weightedInverseCompression (edgeEmbedding (cube size))
    FiniteStencil.frozenEdgeCoefficientQ 13 (by norm_num) FiniteStencil.frozenEdgeCoefficientQ_abs
    (dyadicCandidate index) (coordinateWeight (cube size)) mode = eigenvalue • mode
  eigenvalue_gt : 22 < eigenvalue
  mode_simple : Module.finrank ℝ (eigenspace
    (FiniteStencil.weightedInverseCompression (edgeEmbedding (cube size))
      FiniteStencil.frozenEdgeCoefficientQ 13 (by norm_num) FiniteStencil.frozenEdgeCoefficientQ_abs
      (dyadicCandidate index) (coordinateWeight (cube size))).toLinearMap eigenvalue) = 1
  source_overlap : (budget : ℝ) < |inner ℝ (conventionalCubeSource size S.eigenvector) mode| ^ 2
  refinementPlan : ModeRefinementPlan (edges (cube size)).card
  refinement_error : ∀ b,
    ‖rationalVector (refinementPlan.approximation
      (scalarBinaryCompression (cube size) FiniteStencil.frozenEdgeCoefficientQ
        (dyadicCandidate index) normBound gap gap_pos normBound_pos gap_le)
      (1 + 2 * gap⁻¹) b)‖ ≤ 1 ∧
    ‖rationalVector (refinementPlan.approximation
      (scalarBinaryCompression (cube size) FiniteStencil.frozenEdgeCoefficientQ
        (dyadicCandidate index) normBound gap gap_pos normBound_pos gap_le)
      (1 + 2 * gap⁻¹) b) - mode‖ ≤ (1 / 2 : ℝ)^b
  physical_mode : ∃ y : Field, y ≠ 0 ∧
    perturbedOperator (cube size) (fun e => (FiniteStencil.frozenEdgeCoefficientQ e : ℝ))
      eigenvalue⁻¹ 13 (by norm_num) FiniteStencil.frozenEdgeCoefficientQ_abs y =
        (dyadicCandidate index : ℂ) • y ∧
    Module.finrank ℂ (eigenspace
      (perturbedOperator (cube size) (fun e => (FiniteStencil.frozenEdgeCoefficientQ e : ℝ))
        eigenvalue⁻¹ 13 (by norm_num) FiniteStencil.frozenEdgeCoefficientQ_abs).toLinearMap
      (dyadicCandidate index : ℂ)) = 1
  placement : Matrix (Fin 3) (Fin 3) ℤ
  placement_isUnit : IsUnit (integerPlacementReal placement)
  greenCutoff : ℝ
  greenBudget : ℝ
  greenCutoff_pos : 0 < greenCutoff
  greenBudget_pos : 0 < greenBudget
  energy_distance : pointEnergy - (dyadicCandidate index : ℝ) < greenCutoff
  numerator_budget : greenBudget * Real.sqrt (pointEnergy - (dyadicCandidate index : ℝ)) <
    (budget : ℝ)
  spacing : ∀ minimum : ℕ, ∃ (P : SpacingPlatform) (C₀ : ℚ),
    P.c = 1 ∧ 1 ≤ C₀ ∧ 256 * C₀ ≤ P.errorConstant ∧ minimum ≤ P.minimumDistance ∧
    (∀ n : Site,
      ‖weightedBlock (edgeEmbedding (cube size)) (coordinateWeight (cube size))
        (Ring.inverse (FiniteStencil.frozenOperator (dyadicCandidate index))) (placement.mulVec n)‖ ≤
          (C₀ : ℝ) * (P.r : ℝ) ^ latticeLength n) ∧
    ∀ d ≥ P.minimumDistance, ∀ j : Fin 3,
      (P.a : ℝ) ^ d ≤ ‖inner ℂ (realCoordinateEmbedding mode)
        (weightedBlock (edgeEmbedding (cube size)) (coordinateWeight (cube size))
          (Ring.inverse (FiniteStencil.frozenOperator (dyadicCandidate index)))
          ((d : ℤ) • (fun i => placement i j)) (realCoordinateEmbedding mode))‖

/-- All finite selection data and the physical Green family are derived
from the actual finite spectral hypotheses. The Green threshold is fixed
before the dyadic energy and the accepted mode are chosen. -/
theorem exists_conventional_certified_cube
    (hgap : PointClusterComplementGap) (hexclude : PointOtherSectorExclusion)
    (hglobal : PointRealEdgeExclusion) :
    ∃ S : PhysicalSimpleEdgeData Concrete.material pointEnergy conventionalPointMomentum,
      Nonempty (ConventionalCertifiedCube S) := by
  obtain ⟨S, hSφ, hu, hrealφ, hlower, heven, hreal, halg, haug⟩ :=
    exists_conventional_physical_edge_data hgap hexclude hglobal
  obtain ⟨L, hL, S₀, κ, R, ρ, hκ, hR, hρ, hself, hexp, _, hRayleigh⟩ :=
    exists_conventional_cube_high_rayleigh S hu hrealφ hlower heven hreal halg haug
      22 13 (by norm_num) conventional_coefficient_bound
  obtain ⟨B, ξ₀, greenBudget, hB, hξ₀, hgreenBudget, hgreen⟩ :=
    S.exists_physical_spacing_family (edgeEmbedding (cube L)) (coordinateWeight (cube L))
      13 (by norm_num) conventional_coefficient_bound
  obtain ⟨δ₀, hδ₀, hgap₀⟩ := S.exists_real_gap
  obtain ⟨q, β, sourceBound, hq, hβ, hw, hsourceBound⟩ :=
    exists_conventionalCubeSource_sequence L hgap hexclude S.eigenvector hSφ
  have hunit (z : ℚ) (_hz : 0 < (z : ℝ)) (hze : (z : ℝ) < pointEnergy)
      (hcut : pointEnergy - (z : ℝ) < min ξ₀ δ₀) :
      IsUnit (FiniteStencil.operator FiniteStencil.frozenEdgeCoefficientQ 13
        (by norm_num) FiniteStencil.frozenEdgeCoefficientQ_abs z) := by
    have hz := hgap₀ (pointEnergy - (z : ℝ)) (sub_pos.mpr hze)
      (hcut.trans_le (min_le_right _ _))
    rw [sub_sub_cancel] at hz
    have hi := electric_shift_isUnit_of_fibers (PeriodicYee.edgeAverage Concrete.material)
      13 (by norm_num) conventional_coefficient_bound (z : ℝ) hz
    change IsUnit (FiniteStencil.frozenOperator z)
    rw [FiniteStencil.frozenOperator_binding]
    change IsUnit (electricOperator (periodicCoefficient (PeriodicYee.edgeAverage Concrete.material))
      13 (by norm_num) conventional_coefficient_bound - (z : ℂ) • 1)
    simpa only [Complex.ofReal_ratCast] using hi
  have hedge : 0 < pointEnergy := lt_of_lt_of_le (by norm_num) pointEnergy_range.1
  obtain ⟨index, hiz, hie, hcut, M, δ, budget, hM, hδ, hδM, hb, hnorm, hspec,
      hbudget, stage, hcheck, _⟩ :=
    sqrt_expansion_finite_selection (cube L) FiniteStencil.frozenEdgeCoefficientQ
      13 (by norm_num) FiniteStencil.frozenEdgeCoefficientQ_abs
      (conventionalCubePath L S₀) (conventionalCubeSource L S.eigenvector)
      κ R (ρ / 2) pointEnergy greenBudget (min ξ₀ δ₀) 22
      hκ hR (half_pos hρ) hedge (lt_min hξ₀ hδ₀) (by norm_num)
      (conventionalCubePath_symmetric L S₀ hself)
      (by simpa only [conventionalCubeSource, conventionalCubePath_zero, Rat.cast_ofNat] using hRayleigh)
      (fun ξ hξ hξρ => conventionalCubePath_expansion L S₀ S.eigenvector hrealφ κ R ρ
        hexp ξ hξ (by linarith))
      (fun z _hz hze => conventionalCubePath_binding L S₀ z hze) hunit
      q β sourceBound hq hβ hw hsourceBound
  obtain ⟨μ, u, hunitu, he, hμ, hsimple, hoverlap, plan, hplan⟩ :=
    scalarModeBudgetCheck_refinement (cube L) FiniteStencil.frozenEdgeCoefficientQ
      13 (by norm_num) FiniteStencil.frozenEdgeCoefficientQ_abs
      (dyadicCandidate index) M δ 22 budget hδ hM hδM hnorm hspec
      (conventionalCubeSource L S.eigenvector) q β sourceBound hq hw stage hcheck
  have hphysical := actual_simple_compression_gives_defect (cube L)
    FiniteStencil.frozenEdgeCoefficientQ 13 (by norm_num)
    FiniteStencil.frozenEdgeCoefficientQ_abs (dyadicCandidate index)
    (hunit _ hiz hie hcut) u μ (by norm_num at hμ; linarith) hunitu he hsimple
  have hnorm' : ‖FiniteStencil.frozenOperator (dyadicCandidate index)‖ ≤ (M : ℝ) := hnorm
  have hspec' : ∀ x ∈ spectrum ℝ (FiniteStencil.frozenOperator (dyadicCandidate index)),
      (δ : ℝ) ≤ |x| := hspec
  let : IsometricContinuousFunctionalCalculus ℝ (Field →L[ℂ] Field) IsSelfAdjoint :=
    IsSelfAdjoint.instIsometricContinuousFunctionalCalculus
  obtain ⟨hi, hinv⟩ := inverse_norm_of_spectral_gap
    (FiniteStencil.operator FiniteStencil.frozenEdgeCoefficientQ 13
      (by norm_num) FiniteStencil.frozenEdgeCoefficientQ_abs (dyadicCandidate index))
    (FiniteStencil.operator_selfAdjoint FiniteStencil.frozenEdgeCoefficientQ 13
      (by norm_num) FiniteStencil.frozenEdgeCoefficientQ_abs (dyadicCandidate index))
    (δ : ℝ) (by exact_mod_cast hδ) hspec'
  have hzupper : dyadicCandidate index ≤ 957 / 100000 := by
    have hh : (dyadicCandidate index : ℝ) ≤ ((957 / 100000 : ℚ) : ℝ) := by
      norm_num only [Rat.cast_div, Rat.cast_ofNat]
      exact hie.le.trans pointEnergy_range.2
    exact_mod_cast hh
  have hξ : 0 < pointEnergy - (dyadicCandidate index : ℝ) := sub_pos.mpr hie
  have hξsmall : pointEnergy - (dyadicCandidate index : ℝ) < ξ₀ :=
    hcut.trans_le (min_le_left _ _)
  have hsource : greenBudget * Real.sqrt (pointEnergy - (dyadicCandidate index : ℝ)) <
      ‖inner ℂ S.eigenvector
        (sourceRight (edgeEmbedding (cube L)) (coordinateWeight (cube L))
          (complexifyCoordinates conventionalPointMomentum) (realCoordinateEmbedding u))‖ ^ 2 := by
    have hh := coherent_source_overlap_real L S.eigenvector hrealφ conventionalPointMomentum
      conventional_point_center_trim u
    change greenBudget * Real.sqrt (pointEnergy - (dyadicCandidate index : ℝ)) <
      ‖inner ℂ S.eigenvector
        (sourceRight (edgeEmbedding (cube L)) (coordinateWeight (cube L))
          (realMomentum conventionalPointMomentum) (realCoordinateEmbedding u))‖ ^ 2
    rw [hh, Complex.norm_real, Real.norm_eq_abs]
    exact hbudget.trans hoverlap
  have hfamily := (hgreen _ hξ hξsmall (realCoordinateEmbedding u)
    ((realCoordinateEmbedding.norm_map u).trans hunitu) hsource).2
  have hop : electricOperator (periodicCoefficient (PeriodicYee.edgeAverage Concrete.material))
      13 (by norm_num) conventional_coefficient_bound -
      ((pointEnergy - (pointEnergy - (dyadicCandidate index : ℝ)) : ℝ) : ℂ) • 1 =
        FiniteStencil.frozenOperator (dyadicCandidate index) := by
    rw [sub_sub_cancel, FiniteStencil.frozenOperator_binding]
    simp only [Complex.ofReal_ratCast]
    rfl
  simp only [hop] at hfamily
  refine ⟨S, ⟨{
    size := L, size_ge := hL, index := index,
    energy_pos := hiz, energy_lt_edge := hie, energy_upper := hzupper,
    normBound := M, gap := δ, budget := budget,
    normBound_pos := hM, gap_pos := hδ, gap_le := hδM, budget_pos := hb,
    operator_norm := hnorm', spectral_gap := hspec', operator_isUnit := hi,
    inverse_norm := by simpa only [FiniteStencil.frozenOperator, one_div] using hinv,
    sourceSequence := q, sourceError := β, sourceBound := sourceBound,
    source_enclosure := hq, source_error_tendsto := hβ, source_bound := hw,
    sourceBound_pos := hsourceBound, stage := stage, accepted := hcheck,
    eigenvalue := μ, mode := u, mode_unit := hunitu, mode_equation := he,
    eigenvalue_gt := by exact_mod_cast hμ, mode_simple := hsimple, source_overlap := hoverlap,
    refinementPlan := plan, refinement_error := hplan,
    physical_mode := hphysical, placement := B, placement_isUnit := hB,
    greenCutoff := ξ₀, greenBudget := greenBudget, greenCutoff_pos := hξ₀,
    greenBudget_pos := hgreenBudget, energy_distance := hξsmall,
    numerator_budget := hbudget, spacing := hfamily }⟩⟩

end
end Maxwell.Defect.ScalarDefect
