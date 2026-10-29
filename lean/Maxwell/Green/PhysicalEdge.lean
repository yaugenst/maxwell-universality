import Maxwell.Green.PhysicalMajorant
import Maxwell.Green.CenteredPhysicalFourier

/-! Assembly of the physical Green theorem from one actual conventional
eigenbranch, projector and regular resolvent. All analytic witnesses in this
interface refer to the same concrete finite Maxwell operator. -/

noncomputable section

namespace Maxwell.Green

open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Spectral.Bloch
open PhysicalAnalytic PhysicalLower SourceProfile Filter Set Metric InnerProductSpace
open scoped Topology InnerProductSpace ComplexConjugate

set_option maxHeartbeats 600000

abbrev ConventionalField := EuclideanSpace ℂ Edge20

theorem exists_angular_representative (t : Torus) :
    ∃ q ∈ torusCube (-Real.pi) (2 * Real.pi), angularTorusPoint q = t := by
  let x : Fin 3 → ℝ := fun i => AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ)) (t i)
  let q : RealTorusCoordinates := fun i => (2 * Real.pi) * x i
  refine ⟨q, ?_, ?_⟩
  · intro i
    have hi := (AddCircle.equivIoc (1 : ℝ) (-(1 / 2 : ℝ)) (t i)).property
    change -(1 / 2 : ℝ) < x i ∧ x i ≤ -(1 / 2 : ℝ) + 1 at hi
    change -Real.pi ≤ (2 * Real.pi) * x i ∧ (2 * Real.pi) * x i ≤ -Real.pi + 2 * Real.pi
    constructor <;> nlinarith [Real.pi_pos]
  · ext i
    change (((2 * Real.pi) * x i / (2 * Real.pi) : ℝ) : UnitAddCircle) = t i
    rw [mul_div_cancel_left₀ _ (by positivity : (2 * Real.pi : ℝ) ≠ 0)]
    exact AddCircle.coe_equivIoc

/-- The angular cube covers the entire Haar torus. Actual complex
invertibility on the real cube is therefore the whole real-fiber gap. -/
theorem real_torus_gap_of_centered_inverse (material : Cell20 → ℝ) (E : ℝ)
    (θ : RealTorusCoordinates)
    (hI : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi),
      (shiftedOperator material E (complexifyCoordinates θ + complexifyCoordinates q)).IsInvertible) :
    ∀ t : Torus, E ∉ spectrum ℝ (torusElectric (PeriodicYee.edgeAverage material) t) := by
  intro t
  obtain ⟨q, hq, ht⟩ := exists_angular_representative (t - angularTorusPoint θ)
  have he : angularTorusPoint (θ + q) = t := by
    rw [angularTorusPoint_add, ht, add_sub_cancel]
  have hi := hI q hq
  have hadd : complexifyCoordinates θ + complexifyCoordinates q = complexifyCoordinates (θ + q) :=
    (map_add complexifyCLM θ q).symm
  rw [hadd, shiftedOperator_real, he] at hi
  obtain ⟨e, heq⟩ := hi
  have hu : IsUnit (Matrix.toEuclideanCLM (n := Edge20) (𝕜 := ℂ)
      (torusElectric (PeriodicYee.edgeAverage material) t - (E : ℂ) • 1)) :=
    heq ▸ e.toUnit.isUnit
  have hm : IsUnit (torusElectric (PeriodicYee.edgeAverage material) t - (E : ℂ) • 1) := by
    have h := hu.map (Matrix.toEuclideanCLM (n := Edge20) (𝕜 := ℂ)).symm.toMonoidHom
    change IsUnit ((Matrix.toEuclideanCLM (n := Edge20) (𝕜 := ℂ)).symm
      (Matrix.toEuclideanCLM (n := Edge20) (𝕜 := ℂ)
        (torusElectric (PeriodicYee.edgeAverage material) t - (E : ℂ) • 1))) at h
    simpa only [StarAlgEquiv.symm_apply_apply] using h
  apply spectrum.notMem_iff.mpr
  have hs : E • (1 : Matrix Edge20 Edge20 ℂ) = (E : ℂ) • (1 : Matrix Edge20 Edge20 ℂ) := by
    ext i j
    exact Complex.real_smul
  simpa only [neg_sub, Algebra.algebraMap_eq_smul_one, hs] using hm.neg

/-- Local spectral conclusions for one and the same physical conventional
fiber. These are finite-dimensional spectral facts, not Green estimates. -/
structure PhysicalSimpleEdgeData (material : Cell20 → ℝ) (edge : ℝ)
    (θ : RealTorusCoordinates) where
  value : ComplexTorusCoordinates → ℂ
  projector : ComplexTorusCoordinates → ConventionalField →L[ℂ] ConventionalField
  regular : ComplexTorusCoordinates × ℂ → ConventionalField →L[ℂ] ConventionalField
  eigenvector : ConventionalField
  value_zero : value 0 = (edge : ℂ)
  projector_zero : projector 0 = rankOne ℂ eigenvector eigenvector
  value_analytic : AnalyticAt ℂ value 0
  projector_analytic : AnalyticAt ℂ projector 0
  regular_analytic : AnalyticAt ℂ regular (0, 0)
  stationary : fderiv ℂ value 0 = 0
  hessian_positive : ∀ x : MomentumSpace, x ≠ 0 → 0 < momentumHessian value 0 x x
  reflection : ∀ᶠ z in 𝓝 (0 : ComplexTorusCoordinates),
    value (reflectedComplexCoordinates z) = conj (value z)
  resolvent : ∀ᶠ z in 𝓝 ((0, 0) : ComplexTorusCoordinates × ℂ),
    value z.1 ≠ (edge : ℂ) + z.2 →
      (ConventionalAnalytic.operator material (complexifyCoordinates θ + z.1) -
        ((edge : ℂ) + z.2) • 1).IsInvertible ∧
      (ConventionalAnalytic.operator material (complexifyCoordinates θ + z.1) -
        ((edge : ℂ) + z.2) • 1).inverse =
        (value z.1 - ((edge : ℂ) + z.2))⁻¹ • projector z.1 + regular z
  real_exclusion : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 →
    (shiftedOperator material edge (complexifyCoordinates θ + complexifyCoordinates q)).IsInvertible

namespace PhysicalSimpleEdgeData

variable {material : Cell20 → ℝ} {edge : ℝ} {θ : RealTorusCoordinates}
variable (S : PhysicalSimpleEdgeData material edge θ)

theorem real_hessian_positive (q : RealTorusCoordinates) (hq : q ≠ 0) :
    0 < realDirectionForm (complexHessian S.value 0) q q := by
  have hq' : WithLp.toLp 2 q ≠ (0 : MomentumSpace) := by
    intro h
    exact hq (congrArg WithLp.ofLp h)
  exact S.hessian_positive (WithLp.toLp 2 q) hq'

theorem real_resolvent :
    ∀ᶠ z in 𝓝 ((0, 0) : ComplexTorusCoordinates × ℝ),
      S.value z.1 ≠ ((edge - z.2 : ℝ) : ℂ) →
      (shiftedOperator material (edge - z.2) (complexifyCoordinates θ + z.1)).IsInvertible ∧
      (shiftedOperator material (edge - z.2) (complexifyCoordinates θ + z.1)).inverse =
        (S.value z.1 - ((edge - z.2 : ℝ) : ℂ))⁻¹ • S.projector z.1 +
          S.regular (z.1, (-z.2 : ℂ)) := by
  have hc : Continuous (fun z : ComplexTorusCoordinates × ℝ => (z.1, (-z.2 : ℂ))) := by fun_prop
  have he := (hc.continuousAt (x := ((0, 0) : ComplexTorusCoordinates × ℝ))).tendsto.eventually
    (show ∀ᶠ z in 𝓝 (((0 : ComplexTorusCoordinates), (-(0 : ℝ) : ℂ))),
      S.value z.1 ≠ (edge : ℂ) + z.2 →
        (ConventionalAnalytic.operator material (complexifyCoordinates θ + z.1) -
          ((edge : ℂ) + z.2) • 1).IsInvertible ∧
        (ConventionalAnalytic.operator material (complexifyCoordinates θ + z.1) -
          ((edge : ℂ) + z.2) • 1).inverse =
          (S.value z.1 - ((edge : ℂ) + z.2))⁻¹ • S.projector z.1 + S.regular z from
      by simpa using S.resolvent)
  simpa only [shiftedOperator, sub_eq_add_neg, Complex.ofReal_add, Complex.ofReal_neg] using he

theorem exists_complex_exclusion :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ξ : ℝ, |ξ| < δ →
      ∀ β : RealTorusCoordinates, ‖β‖ < δ →
      edge - ξ ≤ (S.value (Complex.I • complexifyCoordinates β)).re →
      ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi),
        (q ≠ 0 ∨ edge - ξ < (S.value (Complex.I • complexifyCoordinates β)).re) →
        (shiftedOperator material (edge - ξ)
          (complexifyCoordinates θ + (complexifyCoordinates q + Complex.I • complexifyCoordinates β))).IsInvertible :=
  exists_physical_complex_exclusion material edge θ S.value S.value_analytic S.real_hessian_positive
    S.reflection (S.real_resolvent.mono (fun _ h hne => (h hne).1)) S.real_exclusion

include S in
theorem exists_real_gap : ∃ δ : ℝ, 0 < δ ∧ ∀ ξ : ℝ, 0 < ξ → ξ < δ →
    ∀ t : Torus, edge - ξ ∉ spectrum ℝ (torusElectric (PeriodicYee.edgeAverage material) t) := by
  obtain ⟨δ, hδ, hI⟩ := S.exists_complex_exclusion
  refine ⟨δ, hδ, ?_⟩
  intro ξ hξ hξδ
  apply real_torus_gap_of_centered_inverse material (edge - ξ) θ
  intro q hq
  have hzero : Complex.I • complexifyCoordinates 0 = 0 := by
    rw [show complexifyCoordinates 0 = 0 from map_zero complexifyCLM, smul_zero]
  have hgap : edge - ξ < (S.value (Complex.I • complexifyCoordinates 0)).re := by
    rw [hzero, S.value_zero, Complex.ofReal_re]
    linarith
  have hi := hI ξ (by simpa only [abs_of_pos hξ] using hξδ) 0
    (by simpa only [norm_zero] using hδ) hgap.le q hq (Or.inr hgap)
  simpa only [hzero, add_zero] using hi

theorem exists_majorant_radius {N : ℕ} (edges : Fin N ↪ Edge) (W : Fin N → ℚ)
    (u : EuclideanSpace ℂ (Fin N)) :
    ∃ η : ℝ, 0 < η ∧ ∀ ξ : ℝ, |ξ| < η →
      ∀ β : RealTorusCoordinates, ‖β‖ < η →
      (∀ t ∈ Icc (0 : ℝ) 1, edge - ξ ≤ (S.value (Complex.I • complexifyCoordinates (t • β))).re) →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 →
        (shiftedOperator material (edge - ξ) (complexifyCoordinates θ + contourShift β t q)).IsInvertible) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) 1,
        ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 →
          ‖scalarDensity edges W material (edge - ξ) u θ (contourShift β t q)‖ ≤
            coordinateBoundaryMajorant C q :=
  exists_physical_contour_majorant_radius edges W material edge u θ S.value S.projector S.regular
    S.value_analytic S.projector_analytic S.regular_analytic S.real_hessian_positive S.reflection
    (S.real_resolvent.mono (fun _ h hne => (h hne).2))

end PhysicalSimpleEdgeData

end Maxwell.Green
