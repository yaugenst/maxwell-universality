import Maxwell.Green.ResolventMajorant
import Maxwell.Green.SpectralLevelBody

/-! Uniform domination along the whole contour homotopy. Compactness is
applied before the contour parameter is fixed. -/

noncomputable section

namespace Maxwell.Green

open Set Filter Metric
open scoped Topology InnerProductSpace

namespace SpectralLevelBodyData

variable {lam : ComplexTorusCoordinates → ℂ} {edge : ℝ} (D : SpectralLevelBodyData lam edge)

theorem level_smul_le {β : MomentumSpace}
    (hβ : β ∈ closedBall (0 : MomentumSpace) D.radius) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    imaginaryMomentumLevel lam edge (t • β) ≤
      t * imaginaryMomentumLevel lam edge β := by
  have h := D.strictConvexOn.convexOn.2
    (mem_closedBall_self D.radius_pos.le) hβ (sub_nonneg.mpr ht.2) ht.1
    (show 1 - t + t = 1 by ring)
  simpa only [smul_zero, zero_add, D.level_zero, smul_eq_mul, mul_zero, zero_add] using h

theorem interior_contour_level_lt {ξ : ℝ} (hξ : 0 < ξ) {β : MomentumSpace}
    (hβ : β ∈ D.body ξ) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    imaginaryMomentumLevel lam edge (t • β) < ξ := by
  have h := D.level_smul_le hβ.1 ⟨ht.1, ht.2.le⟩
  have hm := mul_le_mul_of_nonneg_left hβ.2 ht.1
  have htξ := mul_lt_of_lt_one_left hξ ht.2
  exact h.trans_lt (hm.trans_lt htξ)

theorem interior_contour_real_gap {ξ : ℝ} (hξ : 0 < ξ) {β : MomentumSpace}
    (hβ : β ∈ D.body ξ) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    edge - ξ < (lam (Complex.I • momentumComplex (t • β))).re := by
  have h := D.interior_contour_level_lt hξ hβ ht
  unfold imaginaryMomentumLevel at h
  linarith

end SpectralLevelBodyData

/-- Both pole exclusion and the reciprocal majorant follow from the same
analytic coercivity estimate, uniformly over the small imaginary shifts. -/
theorem analytic_edge_denominator_control
    (lam : ComplexTorusCoordinates → ℂ) (hlam : AnalyticAt ℂ lam 0)
    (hpos : ∀ q : RealTorusCoordinates, q ≠ 0 →
      0 < realDirectionForm (complexHessian lam 0) q q)
    (hsym : ∀ᶠ z in 𝓝 (0 : ComplexTorusCoordinates),
      lam (reflectedComplexCoordinates z) = star (lam z)) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ q β : RealTorusCoordinates, ‖WithLp.toLp 2 q‖ < δ → ‖β‖ < δ → q ≠ 0 →
      ∀ E : ℝ, E ≤ (lam (Complex.I • complexifyCoordinates β)).re →
        lam (complexifyCoordinates q + Complex.I • complexifyCoordinates β) - (E : ℂ) ≠ 0 ∧
        ‖(lam (complexifyCoordinates q + Complex.I • complexifyCoordinates β) - (E : ℂ))⁻¹‖ ≤
          C * inverseSquare (WithLp.toLp 2 q) := by
  obtain ⟨δ₁, c, hδ₁, hc, hquad⟩ := analytic_edge_denominator_quadratic_bound lam hlam hpos hsym
  obtain ⟨δ₂, C, hδ₂, hC, hbound⟩ := analytic_edge_inverseSquare_bound lam hlam hpos hsym
  refine ⟨min δ₁ δ₂, C, lt_min hδ₁ hδ₂, hC, ?_⟩
  intro q β hq hβ hq₀ E hE
  have hqn : ‖q‖ ≤ ‖WithLp.toLp 2 q‖ := norm_coordinates_le_euclidean (WithLp.toLp 2 q)
  have hq₀' : WithLp.toLp 2 q ≠ (0 : Momentum) := by
    intro hz
    exact hq₀ (congrArg WithLp.ofLp hz)
  exact ⟨denominator_ne_zero_of_quadratic_bound lam q β E c hc hq₀ hE
    (hquad q β (hqn.trans_lt (hq.trans_le (min_le_left _ _)))
      (hβ.trans_le (min_le_left _ _)) E),
    hbound (WithLp.toLp 2 q) β (hq.trans_le (min_le_right _ _))
      (hβ.trans_le (min_le_right _ _)) hq₀' E hE⟩

/-- Compact numerator and regular-part bounds are uniform along the entire
closed contour homotopy, as is the bound on the compact far region. -/
theorem exists_uniform_contour_majorant
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (H A B : ℝ × RealTorusCoordinates → V) (z : ℝ × RealTorusCoordinates → ℂ)
    (U K : Set RealTorusCoordinates) (a p CD : ℝ)
    (hU : IsOpen U) (hK : IsCompact K) (hUK : U ⊆ K) (hCD : 0 ≤ CD)
    (hA : ContinuousOn A (Icc (0 : ℝ) 1 ×ˢ K))
    (hB : ContinuousOn B (Icc (0 : ℝ) 1 ×ˢ K))
    (hfar : ContinuousOn H (Icc (0 : ℝ) 1 ×ˢ (torusCube a p \ U)))
    (hlocal : ∀ t ∈ Icc (0 : ℝ) 1, ∀ q ∈ torusCube a p, q ∈ U → q ≠ 0 →
      H (t, q) = (z (t, q))⁻¹ • A (t, q) + B (t, q))
    (hz : ∀ t ∈ Icc (0 : ℝ) 1, ∀ q ∈ torusCube a p, q ∈ U → q ≠ 0 →
      ‖(z (t, q))⁻¹‖ ≤ CD * inverseSquare (WithLp.toLp 2 q)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ q ∈ torusCube a p, q ≠ 0 →
      ‖H (t, q)‖ ≤ coordinateBoundaryMajorant C q := by
  obtain ⟨CA, hCA⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hA
  obtain ⟨CB, hCB⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hB
  obtain ⟨CF, hCF⟩ := (isCompact_Icc.prod
    ((isCompact_torusCube a p).diff hU)).exists_bound_of_continuousOn hfar
  refine ⟨max CA 0 * CD + max CB 0 + max CF 0, by positivity, ?_⟩
  intro t ht
  apply localPole_far_bound_majorant (fun q => H (t, q)) (fun q => A (t, q))
    (fun q => B (t, q)) (fun q => z (t, q)) U
    (max CA 0) (max CB 0) CD (max CF 0) a p
    (le_max_right _ _) (le_max_right _ _) hCD (le_max_right _ _) (hlocal t ht)
  · intro q _ hq _
    exact (hCA (t, q) ⟨ht, hUK hq⟩).trans (le_max_left _ _)
  · intro q _ hq _
    exact (hCB (t, q) ⟨ht, hUK hq⟩).trans (le_max_left _ _)
  · exact hz t ht
  · intro q hq hqU
    exact (hCF (t, q) ⟨ht, hq, hqU⟩).trans (le_max_left _ _)

/-- A local pole identity and local reciprocal estimate need only hold as
germs. The compact chart and all amplitude constants are constructed. -/
theorem exists_majorant_of_local_pole_germ
    (H A B : RealTorusCoordinates → ℂ) (z : RealTorusCoordinates → ℂ)
    (a p CD : ℝ) (hCD : 0 ≤ CD)
    (hA : ContinuousAt A 0) (hB : ContinuousAt B 0)
    (hH : ∀ q ∈ torusCube a p, q ≠ 0 → ContinuousAt H q)
    (hpole : ∀ᶠ q in 𝓝 (0 : RealTorusCoordinates), q ≠ 0 →
      H q = (z q)⁻¹ * A q + B q)
    (hz : ∀ᶠ q in 𝓝 (0 : RealTorusCoordinates), q ≠ 0 →
      ‖(z q)⁻¹‖ ≤ CD * inverseSquare (WithLp.toLp 2 q)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ torusCube a p, q ≠ 0 →
      ‖H q‖ ≤ coordinateBoundaryMajorant C q := by
  have hnearA : ∀ᶠ q in 𝓝 (0 : RealTorusCoordinates), ‖A q‖ < ‖A 0‖ + 1 :=
    hA.norm.eventually (gt_mem_nhds (by linarith))
  have hnearB : ∀ᶠ q in 𝓝 (0 : RealTorusCoordinates), ‖B q‖ < ‖B 0‖ + 1 :=
    hB.norm.eventually (gt_mem_nhds (by linarith))
  obtain ⟨r, hr, hlocal⟩ := Metric.eventually_nhds_iff_ball.mp
    (hpole.and (hz.and (hnearA.and hnearB)))
  have hfar : ContinuousOn H (torusCube a p \ ball 0 r) := by
    intro q hq
    exact (hH q hq.1 (fun he => hq.2 (he ▸ mem_ball_self hr))).continuousWithinAt
  obtain ⟨CF, hCF⟩ := ((isCompact_torusCube a p).diff isOpen_ball).exists_bound_of_continuousOn hfar
  refine ⟨(‖A 0‖ + 1) * CD + (‖B 0‖ + 1) + max CF 0, by positivity, ?_⟩
  apply localPole_far_bound_majorant H A B z (ball 0 r)
    (‖A 0‖ + 1) (‖B 0‖ + 1) CD (max CF 0) a p
    (by positivity) (by positivity) hCD (le_max_right _ _)
  · intro q _ hq hq₀
    exact (hlocal q hq).1 hq₀
  · intro q _ hq _
    exact (hlocal q hq).2.2.1.le
  · intro q _ hq _
    exact (hlocal q hq).2.2.2.le
  · intro q _ hq hq₀
    exact (hlocal q hq).2.1 hq₀
  · intro q hq hqU
    exact (hCF q ⟨hq, hqU⟩).trans (le_max_left _ _)

end Maxwell.Green
