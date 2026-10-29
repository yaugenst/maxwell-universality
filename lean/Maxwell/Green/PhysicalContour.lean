import Maxwell.Green.PhysicalAnalytic
import Maxwell.Green.UniformContour

/-! Complex spectral exclusions for the actual conventional Maxwell fiber.
Compact real separation controls the far region; the constructed local
eigenbranch and its positive Hessian control the edge region. -/

noncomputable section

namespace Maxwell.Green.PhysicalAnalytic

open Maxwell.Spectral Maxwell.Spectral.Lattice Set Filter Metric
open scoped Topology ComplexConjugate

set_option maxHeartbeats 600000

theorem compact_far_inverse (material : Cell20 → ℝ) (edge : ℝ)
    (θ : RealTorusCoordinates) (K : Set RealTorusCoordinates) (hK : IsCompact K)
    (hreal : ∀ q ∈ K, (shiftedOperator material edge
      (complexifyCoordinates θ + complexifyCoordinates q)).IsInvertible) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ ∀ ξ : ℝ, |ξ| < r →
      ∀ β : RealTorusCoordinates, ‖β‖ < r → ∀ q ∈ K,
        (shiftedOperator material (edge - ξ)
          (complexifyCoordinates θ + (complexifyCoordinates q + Complex.I • complexifyCoordinates β))).IsInvertible ∧
        ‖(shiftedOperator material (edge - ξ)
          (complexifyCoordinates θ + (complexifyCoordinates q + Complex.I • complexifyCoordinates β))).inverse‖ ≤ C := by
  let F := fun p : (ℝ × RealTorusCoordinates) × RealTorusCoordinates =>
    shiftedOperator material (edge - p.1.1)
      (complexifyCoordinates θ + (complexifyCoordinates p.2 + Complex.I • complexifyCoordinates p.1.2))
  have hcont : Continuous F := by
    apply Continuous.sub
    · have hA : Continuous (ConventionalAnalytic.operator material) :=
        continuous_iff_continuousAt.mpr fun z =>
          (ConventionalAnalytic.operator_analyticAt material z).continuousAt
      apply hA.comp
      change Continuous (fun p : (ℝ × RealTorusCoordinates) × RealTorusCoordinates =>
        fun j => (θ j : ℂ) + ((p.2 j : ℂ) + Complex.I * (p.1.2 j : ℂ)))
      fun_prop
    · exact ((Complex.continuous_ofReal.comp
        (continuous_const.sub (continuous_fst.comp continuous_fst))).smul continuous_const)
  have hFzero (q : RealTorusCoordinates) : F (0, q) = shiftedOperator material edge
      (complexifyCoordinates θ + complexifyCoordinates q) := by
    change shiftedOperator material (edge - 0)
      (complexifyCoordinates θ + (complexifyCoordinates q + Complex.I • complexifyCoordinates 0)) = _
    rw [sub_zero, show complexifyCoordinates 0 = 0 from map_zero complexifyCLM,
      smul_zero, add_zero]
  obtain ⟨r, C, hr, hC, h⟩ := ComplexContourGap.compact_inverse_neighborhood K hK F
    (fun _ _ => hcont.continuousAt) (fun q hq => by rw [hFzero]; exact hreal q hq)
  refine ⟨r, C, hr, hC, ?_⟩
  intro ξ hξ β hβ q hq
  have hn : ‖(ξ, β)‖ < r := by
    simpa only [Prod.norm_def, Real.norm_eq_abs, max_lt_iff] using (And.intro hξ hβ)
  exact h (ξ, β) hn q hq

/-- Local analyticity and real-fiber exclusion outside the edge produce
actual complex invertibility on the entire shifted torus. In the boundary
case only the edge point itself is exceptional. -/
theorem exists_physical_complex_exclusion
    (material : Cell20 → ℝ) (edge : ℝ) (θ : RealTorusCoordinates)
    (lam : ComplexTorusCoordinates → ℂ) (hlam : AnalyticAt ℂ lam 0)
    (hpos : ∀ q : RealTorusCoordinates, q ≠ 0 →
      0 < realDirectionForm (complexHessian lam 0) q q)
    (hsym : ∀ᶠ z in 𝓝 (0 : ComplexTorusCoordinates),
      lam (reflectedComplexCoordinates z) = conj (lam z))
    (hlocal : ∀ᶠ z in 𝓝 ((0, 0) : ComplexTorusCoordinates × ℝ),
      lam z.1 ≠ ((edge - z.2 : ℝ) : ℂ) →
      (shiftedOperator material (edge - z.2)
        (complexifyCoordinates θ + z.1)).IsInvertible)
    (hreal : ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 →
      (shiftedOperator material edge
        (complexifyCoordinates θ + complexifyCoordinates q)).IsInvertible) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ξ : ℝ, |ξ| < δ →
      ∀ β : RealTorusCoordinates, ‖β‖ < δ →
      edge - ξ ≤ (lam (Complex.I • complexifyCoordinates β)).re →
      ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi),
        (q ≠ 0 ∨ edge - ξ < (lam (Complex.I • complexifyCoordinates β)).re) →
        (shiftedOperator material (edge - ξ)
          (complexifyCoordinates θ + (complexifyCoordinates q + Complex.I • complexifyCoordinates β))).IsInvertible := by
  obtain ⟨rL, hrL, hL⟩ := Metric.eventually_nhds_iff_ball.mp hlocal
  obtain ⟨rH, c, hrH, hc, hquad⟩ := analytic_edge_denominator_quadratic_bound lam hlam hpos hsym
  let r : ℝ := min rL rH / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrL' : r ≤ rL / 4 := by dsimp [r]; gcongr; exact min_le_left _ _
  have hrH' : r ≤ rH / 4 := by dsimp [r]; gcongr; exact min_le_right _ _
  let K := torusCube (-Real.pi) (2 * Real.pi) \ ball (0 : RealTorusCoordinates) r
  have hK : IsCompact K := (isCompact_torusCube _ _).diff isOpen_ball
  obtain ⟨rF, C, hrF, _, hfar⟩ := compact_far_inverse material edge θ K hK
    (fun q hq => hreal q hq.1 (fun hq₀ => hq.2 (hq₀ ▸ mem_ball_self hr)))
  refine ⟨min r rF, lt_min hr hrF, ?_⟩
  intro ξ hξ β hβ hgap q hq hqgap
  by_cases hqr : q ∈ ball (0 : RealTorusCoordinates) r
  · have hqn : ‖q‖ < r := mem_ball_zero_iff.mp hqr
    have hβr : ‖β‖ < r := hβ.trans_le (min_le_left _ _)
    have hξr : |ξ| < r := hξ.trans_le (min_le_left _ _)
    have hne : lam (complexifyCoordinates q + Complex.I • complexifyCoordinates β) -
        ((edge - ξ : ℝ) : ℂ) ≠ 0 := by
      have hqH : ‖q‖ < rH := by linarith
      have hβH : ‖β‖ < rH := by linarith
      rcases hqgap with hq₀ | hg
      · exact denominator_ne_zero_of_quadratic_bound lam q β (edge - ξ) c hc hq₀ hgap
          (hquad q β hqH hβH (edge - ξ))
      · exact denominator_ne_zero_of_strict_gap lam q β (edge - ξ) c hc.le hg
          (hquad q β hqH hβH (edge - ξ))
    have hsmall : (complexifyCoordinates q + Complex.I • complexifyCoordinates β, ξ) ∈
        ball ((0, 0) : ComplexTorusCoordinates × ℝ) rL := by
      change (complexifyCoordinates q + Complex.I • complexifyCoordinates β, ξ) ∈
        ball (0 : ComplexTorusCoordinates × ℝ) rL
      rw [mem_ball_zero_iff]
      rw [Prod.norm_def, max_lt_iff]
      constructor
      · have hnorm := norm_add_le (complexifyCoordinates q) (Complex.I • complexifyCoordinates β)
        rw [norm_complexifyCoordinates, norm_imaginary_coordinates] at hnorm
        linarith
      · simp only [Real.norm_eq_abs]
        linarith
    apply hL (complexifyCoordinates q + Complex.I • complexifyCoordinates β, ξ) hsmall
    exact sub_ne_zero.mp hne
  · exact (hfar ξ (hξ.trans_le (min_le_right _ _)) β
      (hβ.trans_le (min_le_right _ _)) q ⟨hq, hqr⟩).1

/-- The actual convex spectral body puts every interior contour strictly
in the resolvent region, while its endpoint has only the single pole. -/
theorem physical_contour_invertibility_of_body
    (material : Cell20 → ℝ) (edge : ℝ) (θ : RealTorusCoordinates)
    (lam : ComplexTorusCoordinates → ℂ) (D : SpectralLevelBodyData lam edge)
    (δ : ℝ) (hDδ : D.radius < δ)
    (hI : ∀ ξ : ℝ, |ξ| < δ → ∀ γ : RealTorusCoordinates, ‖γ‖ < δ →
      edge - ξ ≤ (lam (Complex.I • complexifyCoordinates γ)).re →
      ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi),
        (q ≠ 0 ∨ edge - ξ < (lam (Complex.I • complexifyCoordinates γ)).re) →
        (shiftedOperator material (edge - ξ)
          (complexifyCoordinates θ + (complexifyCoordinates q + Complex.I • complexifyCoordinates γ))).IsInvertible)
    {ξ : ℝ} (hξ : 0 < ξ) (hξδ : ξ < δ) {β : MomentumSpace} (hβ : β ∈ D.body ξ) :
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi), q ≠ 0 →
      (shiftedOperator material (edge - ξ)
        (complexifyCoordinates θ + contourShift β.ofLp t q)).IsInvertible) ∧
    (∀ t ∈ Ico (0 : ℝ) 1, ∀ q ∈ torusCube (-Real.pi) (2 * Real.pi),
      (shiftedOperator material (edge - ξ)
        (complexifyCoordinates θ + contourShift β.ofLp t q)).IsInvertible) := by
  have hnorm {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : ‖(t • β).ofLp‖ < δ := by
    have hβn := mem_closedBall_zero_iff.mp hβ.1
    calc
      _ ≤ ‖t • β‖ := norm_coordinates_le_euclidean (t • β)
      _ = t * ‖β‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      _ ≤ ‖β‖ := mul_le_of_le_one_left (norm_nonneg _) ht.2
      _ < δ := hβn.trans_lt hDδ
  have hgap {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      edge - ξ ≤ (lam (Complex.I • complexifyCoordinates (t • β).ofLp)).re := by
    have hlev := D.level_smul_le hβ.1 ht
    have hmul := mul_le_mul_of_nonneg_left hβ.2 ht.1
    have hscale := mul_le_of_le_one_left hξ.le ht.2
    change edge - (lam (Complex.I • momentumComplex (t • β))).re ≤
      t * imaginaryMomentumLevel lam edge β at hlev
    change edge - ξ ≤ (lam (Complex.I • momentumComplex (t • β))).re
    linarith
  have hpoint {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {q : RealTorusCoordinates}
      (hq : q ∈ torusCube (-Real.pi) (2 * Real.pi))
      (hne : q ≠ 0 ∨ edge - ξ < (lam (Complex.I • momentumComplex (t • β))).re) :
      (shiftedOperator material (edge - ξ)
        (complexifyCoordinates θ + contourShift β.ofLp t q)).IsInvertible := by
    rw [contourShift_rescale]
    exact hI ξ (by simpa only [abs_of_pos hξ] using hξδ) (t • β).ofLp
      (hnorm ht) (hgap ht) q hq hne
  exact ⟨fun _ ht _ hq hq₀ => hpoint ht hq (Or.inl hq₀),
    fun _ ht _ hq => hpoint ⟨ht.1, ht.2.le⟩ hq
      (Or.inr (D.interior_contour_real_gap hξ hβ ht))⟩

end Maxwell.Green.PhysicalAnalytic
