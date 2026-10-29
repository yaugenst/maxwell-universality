import Maxwell.Green.PhysicalLower
import Maxwell.Green.PhysicalContour

/-! A uniform contour majorant for the actual weighted source density,
derived from the same jointly analytic resolvent decomposition. -/

noncomputable section

namespace Maxwell.Green.PhysicalLower

open Maxwell.Spectral Maxwell.Spectral.Lattice Maxwell.Spectral.Bloch
open SourceProfile PhysicalAnalytic Filter Set Metric
open scoped Topology ComplexConjugate

variable {N : ℕ}

set_option maxHeartbeats 600000

theorem euclidean_coordinates_norm_le_three (q : RealTorusCoordinates) :
    ‖WithLp.toLp 2 q‖ ≤ 3 * ‖q‖ := by
  have h := euclidean_norm_sq_le_three_coordinates (WithLp.toLp 2 q)
  change ‖WithLp.toLp 2 q‖ ^ 2 ≤ 3 * ‖q‖ ^ 2 at h
  have hn := norm_nonneg q
  nlinarith [norm_nonneg (WithLp.toLp 2 q)]

theorem norm_contourShift_le (β q : RealTorusCoordinates) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : ‖contourShift β t q‖ ≤ ‖q‖ + ‖β‖ := by
  unfold contourShift
  calc
    _ ≤ ‖complexifyCoordinates q‖ + ‖t • (Complex.I • complexifyCoordinates β)‖ := norm_add_le _ _
    _ = ‖q‖ + t * ‖β‖ := by
      rw [norm_complexifyCoordinates, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg ht.1, norm_imaginary_coordinates]
    _ ≤ _ := add_le_add_right (mul_le_of_le_one_left (norm_nonneg β) ht.2) _

/-- All constants are derived uniformly before the operating shift and
the boundary support point are chosen. -/
theorem exists_physical_contour_majorant_radius_uniform
    (edges : Fin N ↪ Edge) (W : Fin N → ℚ) (material : Cell20 → ℝ)
    (edge : ℝ) (θ : RealTorusCoordinates)
    (lam : ComplexTorusCoordinates → ℂ)
    (P : ComplexTorusCoordinates → EuclideanSpace ℂ Edge20 →L[ℂ] EuclideanSpace ℂ Edge20)
    (R : ComplexTorusCoordinates × ℂ → EuclideanSpace ℂ Edge20 →L[ℂ] EuclideanSpace ℂ Edge20)
    (hlam : AnalyticAt ℂ lam 0) (hP : AnalyticAt ℂ P 0) (hR : AnalyticAt ℂ R (0, 0))
    (hpos : ∀ q : RealTorusCoordinates, q ≠ 0 →
      0 < realDirectionForm (complexHessian lam 0) q q)
    (hsym : ∀ᶠ z in 𝓝 (0 : ComplexTorusCoordinates),
      lam (reflectedComplexCoordinates z) = conj (lam z))
    (hpole : ∀ᶠ z in 𝓝 ((0, 0) : ComplexTorusCoordinates × ℝ),
      lam z.1 ≠ ((edge - z.2 : ℝ) : ℂ) →
      (shiftedOperator material (edge - z.2) (complexifyCoordinates θ + z.1)).inverse =
        (lam z.1 - ((edge - z.2 : ℝ) : ℂ))⁻¹ • P z.1 + R (z.1, (-z.2 : ℂ))) :
    ∃ η : ℝ, 0 < η ∧ ∀ u : EuclideanSpace ℂ (Fin N), ∀ ξ : ℝ, |ξ| < η →
      ∀ β : RealTorusCoordinates, ‖β‖ < η →
      (∀ t ∈ Icc (0 : ℝ) 1, edge - ξ ≤ (lam (Complex.I • complexifyCoordinates (t • β))).re) →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 →
        (shiftedOperator material (edge - ξ) (complexifyCoordinates θ + contourShift β t q)).IsInvertible) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) 1,
        ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 →
          ‖scalarDensity edges W material (edge - ξ) u θ (contourShift β t q)‖ ≤
            coordinateBoundaryMajorant C q := by
  have hcP : ∀ᶠ z in 𝓝 ((0, 0) : ComplexTorusCoordinates × ℝ), AnalyticAt ℂ P z.1 :=
    continuous_fst.continuousAt.tendsto.eventually hP.eventually_analyticAt
  have hcR : ∀ᶠ z in 𝓝 ((0, 0) : ComplexTorusCoordinates × ℝ),
      AnalyticAt ℂ R (z.1, (-z.2 : ℂ)) := by
    have hc : Continuous (fun z : ComplexTorusCoordinates × ℝ => (z.1, (-z.2 : ℂ))) := by fun_prop
    exact hc.continuousAt.tendsto.eventually (by simpa using hR.eventually_analyticAt)
  obtain ⟨r, hr, hlocal⟩ := Metric.eventually_nhds_iff_ball.mp (hcP.and (hcR.and hpole))
  obtain ⟨δ, CD, hδ, hCD, hden⟩ := analytic_edge_denominator_control lam hlam hpos hsym
  let η : ℝ := min r δ / 10
  have hη : 0 < η := by dsimp [η]; positivity
  have hηr : η ≤ r / 10 := by dsimp [η]; gcongr; exact min_le_left _ _
  have hηδ : η ≤ δ / 10 := by dsimp [η]; gcongr; exact min_le_right _ _
  refine ⟨η, hη, ?_⟩
  intro u ξ hξ β hβ hgap hI
  let H := fun p : ℝ × RealTorusCoordinates =>
    scalarDensity edges W material (edge - ξ) u θ (contourShift β p.1 p.2)
  let A := fun p : ℝ × RealTorusCoordinates =>
    sourceNumerator edges W u θ P (contourShift β p.1 p.2)
  let B := fun p : ℝ × RealTorusCoordinates =>
    sourceNumerator edges W u θ (fun z => R (z, (-ξ : ℂ))) (contourShift β p.1 p.2)
  let z := fun p : ℝ × RealTorusCoordinates => lam (contourShift β p.1 p.2) - ((edge - ξ : ℝ) : ℂ)
  have hsmall {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {q : RealTorusCoordinates}
      (hq : q ∈ closedBall (0 : RealTorusCoordinates) η) :
      (contourShift β t q, ξ) ∈ ball ((0, 0) : ComplexTorusCoordinates × ℝ) r := by
    change (contourShift β t q, ξ) ∈ ball (0 : ComplexTorusCoordinates × ℝ) r
    rw [mem_ball_zero_iff, Prod.norm_def, max_lt_iff]
    have hqn := mem_closedBall_zero_iff.mp hq
    have hn := norm_contourShift_le β q ht
    exact ⟨by linarith, by rw [Real.norm_eq_abs]; linarith⟩
  have htβ {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ‖t • β‖ < δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    have hmul := mul_le_of_le_one_left (norm_nonneg β) ht.2
    linarith
  have hdenq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {q : RealTorusCoordinates}
      (hq : q ∈ ball (0 : RealTorusCoordinates) η) (hq₀ : q ≠ 0) :
      z (t,q) ≠ 0 ∧ ‖(z (t,q))⁻¹‖ ≤ CD * inverseSquare (WithLp.toLp 2 q) := by
    have hqnorm := mem_ball_zero_iff.mp hq
    have hqe : ‖WithLp.toLp 2 q‖ < δ :=
      (euclidean_coordinates_norm_le_three q).trans_lt (by linarith)
    simpa only [z, contourShift_rescale] using hden q (t • β) hqe (htβ ht) hq₀
      (edge - ξ) (hgap t ht)
  apply exists_uniform_contour_majorant H A B z (ball 0 η) (closedBall 0 η)
    (-Real.pi) (2 * Real.pi) CD isOpen_ball (isCompact_closedBall _ _)
    ball_subset_closedBall hCD.le
  · intro p hp
    have ha := sourceNumerator_analyticAt edges W u θ P (hlocal _ (hsmall hp.1 hp.2)).1
    have hcomp := ContinuousAt.comp (x := p) (f := fun p : ℝ × RealTorusCoordinates => contourShift β p.1 p.2)
      (g := sourceNumerator edges W u θ P) ha.continuousAt (continuous_contourShift β).continuousAt
    exact hcomp.continuousWithinAt
  · intro p hp
    have hr' : AnalyticAt ℂ (fun z => R (z, (-ξ : ℂ))) (contourShift β p.1 p.2) :=
      AnalyticAt.comp (g := R) (f := fun z => (z, (-ξ : ℂ)))
        (hlocal _ (hsmall hp.1 hp.2)).2.1 (analyticAt_id.prod analyticAt_const)
    have hb := sourceNumerator_analyticAt edges W u θ _ hr'
    have hcomp := ContinuousAt.comp (x := p) (f := fun p : ℝ × RealTorusCoordinates => contourShift β p.1 p.2)
      (g := sourceNumerator edges W u θ (fun z => R (z, (-ξ : ℂ))))
      hb.continuousAt (continuous_contourShift β).continuousAt
    exact hcomp.continuousWithinAt
  · intro p hp
    have hq₀ : p.2 ≠ 0 := fun hq => hp.2.2 (hq ▸ mem_ball_self hη)
    have hcomp := ContinuousAt.comp (x := p) (f := fun p : ℝ × RealTorusCoordinates => contourShift β p.1 p.2)
      (g := scalarDensity edges W material (edge - ξ) u θ)
      (scalarDensity_analyticAt edges W material (edge - ξ) u θ
        (hI p.1 hp.1 p.2 hp.2.1 hq₀)).continuousAt (continuous_contourShift β).continuousAt
    exact hcomp.continuousWithinAt
  · intro t ht q _ hq hq₀
    have hd := (hdenq ht hq hq₀).1
    have hp := (hlocal _ (hsmall ht (ball_subset_closedBall hq))).2.2 (sub_ne_zero.mp hd)
    have h := scalarDensity_pole edges W material (edge - ξ) u θ lam P
      (fun z => R (z, (-ξ : ℂ))) _ hp
    simpa only [H, A, B, z, smul_eq_mul, div_eq_mul_inv, mul_comm] using h
  · intro t ht q _ hq hq₀
    exact (hdenq ht hq hq₀).2

theorem exists_physical_contour_majorant_radius
    (edges : Fin N ↪ Edge) (W : Fin N → ℚ) (material : Cell20 → ℝ)
    (edge : ℝ) (u : EuclideanSpace ℂ (Fin N)) (θ : RealTorusCoordinates)
    (lam : ComplexTorusCoordinates → ℂ)
    (P : ComplexTorusCoordinates → EuclideanSpace ℂ Edge20 →L[ℂ] EuclideanSpace ℂ Edge20)
    (R : ComplexTorusCoordinates × ℂ → EuclideanSpace ℂ Edge20 →L[ℂ] EuclideanSpace ℂ Edge20)
    (hlam : AnalyticAt ℂ lam 0) (hP : AnalyticAt ℂ P 0) (hR : AnalyticAt ℂ R (0, 0))
    (hpos : ∀ q : RealTorusCoordinates, q ≠ 0 →
      0 < realDirectionForm (complexHessian lam 0) q q)
    (hsym : ∀ᶠ z in 𝓝 (0 : ComplexTorusCoordinates),
      lam (reflectedComplexCoordinates z) = conj (lam z))
    (hpole : ∀ᶠ z in 𝓝 ((0, 0) : ComplexTorusCoordinates × ℝ),
      lam z.1 ≠ ((edge - z.2 : ℝ) : ℂ) →
      (shiftedOperator material (edge - z.2) (complexifyCoordinates θ + z.1)).inverse =
        (lam z.1 - ((edge - z.2 : ℝ) : ℂ))⁻¹ • P z.1 + R (z.1, (-z.2 : ℂ))) :
    ∃ η : ℝ, 0 < η ∧ ∀ ξ : ℝ, |ξ| < η →
      ∀ β : RealTorusCoordinates, ‖β‖ < η →
      (∀ t ∈ Icc (0 : ℝ) 1, edge - ξ ≤ (lam (Complex.I • complexifyCoordinates (t • β))).re) →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 →
        (shiftedOperator material (edge - ξ) (complexifyCoordinates θ + contourShift β t q)).IsInvertible) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) 1,
        ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 →
          ‖scalarDensity edges W material (edge - ξ) u θ (contourShift β t q)‖ ≤
            coordinateBoundaryMajorant C q := by
  obtain ⟨η, hη, hh⟩ := exists_physical_contour_majorant_radius_uniform edges W material edge θ
    lam P R hlam hP hR hpos hsym hpole
  exact ⟨η, hη, hh u⟩

end Maxwell.Green.PhysicalLower
