import Maxwell.Defect.LocalBandChart
import Maxwell.Defect.EvenNumerator

/-! Construction of the local integration chart from the actual analytic
selected eigenvalue and compressed projection. Odd numerator terms are
removed by an exact integral symmetry, and coercivity is proved by
shrinking the radius using the quartic Taylor bound. -/

namespace Maxwell.Defect
open Filter Topology MeasureTheory Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem local_bounded_band_integrable (B : Momentum → F) (d : Momentum → ℝ)
    {r c M ξ : ℝ} (hc : 0 < c) (hξ : 0 ≤ ξ)
    (hBm : AEStronglyMeasurable B (volume.restrict (Metric.ball 0 r)))
    (hdm : Measurable d)
    (hd : ∀ q ∈ Metric.ball 0 r, q ≠ 0 → c * ‖q‖ ^ 2 ≤ d q)
    (hB : ∀ q ∈ Metric.ball 0 r, ‖B q‖ ≤ M) :
    IntegrableOn (fun q => (d q + ξ)⁻¹ • B q) (Metric.ball 0 r) := by
  have hmajor := (inverse_square_integrable_ball r).const_mul (M / c)
  apply hmajor.mono' (((hdm.add_const ξ).inv.aestronglyMeasurable).smul hBm)
  have hne : ∀ᵐ q : Momentum, q ≠ 0 := by simp [ae_iff]
  filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hne] with q hq hq0
  have hr : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  have hdq : 0 < d q + ξ := by nlinarith [hd q hq hq0, sq_pos_of_pos hr]
  change ‖(d q + ξ)⁻¹ • B q‖ ≤ M / c * (1 / ‖q‖ ^ 2)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hdq)]
  calc
    (d q + ξ)⁻¹ * ‖B q‖ ≤ (c * ‖q‖ ^ 2)⁻¹ * M := by
      apply mul_le_mul
      · apply inv_anti₀ (by positivity)
        linarith [hd q hq hq0]
      · exact hB q hq
      · exact norm_nonneg _
      · positivity
    _ = M / c * (1 / ‖q‖ ^ 2) := by field_simp

/-- Every actual analytic even nondegenerate edge has a local integral
chart. The chart dispersion equals the original eigenvalue on its ball;
the original compressed numerator gives exactly the same pole integral. -/
theorem exists_analytic_localBandChart [CompleteSpace F]
    (B : Momentum → F) (d : Momentum → ℝ)
    (p : FormalMultilinearSeries ℝ Momentum ℝ)
    (hB : AnalyticAt ℝ B 0) (hd : HasFPowerSeriesAt d p 0)
    (hd0 : d 0 = 0) (heven : ∀ᶠ q in 𝓝 (0 : Momentum), d (-q) = d q)
    (L : Momentum ≃L[ℝ] Momentum) {c radiusLimit : ℝ}
    (hc : 0 < c) (hlimit : 0 < radiusLimit)
    (hquadratic : ∀ q, p 2 (fun _ => q) = ‖L q‖ ^ 2)
    (hcoercive : ∀ q, c * ‖q‖ ^ 2 ≤ ‖L q‖ ^ 2) :
    ∃ C : LocalBandChart F,
      C.radius ≤ radiusLimit ∧ C.quadraticRoot = L ∧ C.edgeNumerator = B 0 ∧
      C.numerator = evenPart B ∧
      (∀ q ∈ Metric.ball 0 C.radius, C.dispersion q = d q) ∧
      (∀ ξ, 0 ≤ ξ → C.localPart ξ =
        ∫ q in Metric.ball 0 C.radius, (d q + ξ)⁻¹ • B q) ∧
      (∀ ξ, 0 ≤ ξ → IntegrableOn (fun q => (d q + ξ)⁻¹ • B q)
        (Metric.ball 0 C.radius)) := by
  classical
  obtain ⟨N, rN, hN, hrN, hnum⟩ := analytic_evenPart_quadratic B hB
  obtain ⟨D, rD, hD, hrD, hdisp⟩ := analytic_even_quartic d p hd heven
  have hbounded : ∀ᶠ q in 𝓝 (0 : Momentum), ‖B q‖ < ‖B 0‖ + 1 :=
    hB.continuousAt.norm.tendsto.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨r0, hr0, hlocal⟩ := Metric.eventually_nhds_iff.mp
    (hB.eventually_continuousAt.and (hd.analyticAt.eventually_continuousAt.and
      (heven.and hbounded)))
  let r := min rN (min rD (min r0 (min radiusLimit (Real.sqrt (c / (2 * D))))))
  have hr : 0 < r := by dsimp [r]; positivity
  have hrN' : r ≤ rN := min_le_left _ _
  have hrD' : r ≤ rD := (min_le_right _ _).trans (min_le_left _ _)
  have hr0' : r ≤ r0 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hrlimit : r ≤ radiusLimit := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrsqrt : r ≤ Real.sqrt (c / (2 * D)) := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hq0 : ∀ q ∈ Metric.ball (0 : Momentum) r, dist q 0 < r0 := by
    intro q hq
    exact lt_of_lt_of_le hq hr0'
  have hBc : ContinuousOn B (Metric.ball 0 r) := by
    intro q hq
    exact (hlocal (hq0 q hq)).1.continuousWithinAt
  have hdc : ContinuousOn d (Metric.ball 0 r) := by
    intro q hq
    exact (hlocal (hq0 q hq)).2.1.continuousWithinAt
  have hBeven : ContinuousOn (evenPart B) (Metric.ball 0 r) := by
    unfold evenPart
    exact continuousOn_const.smul (hBc.add (hBc.comp continuous_neg.continuousOn
      (fun q hq => by simpa using hq)))
  let d' : Momentum → ℝ := (Metric.ball 0 r).piecewise d (fun _ => 0)
  have hd'eq : ∀ q ∈ Metric.ball 0 r, d' q = d q := by
    intro q hq
    exact Set.piecewise_eq_of_mem _ _ _ hq
  have hd'm : Measurable d' :=
    hdc.measurable_piecewise continuousOn_const measurableSet_ball
  have hquartic : ∀ q ∈ Metric.ball 0 r,
      |d' q - ‖L q‖ ^ 2| ≤ D * ‖q‖ ^ 4 := by
    intro q hq
    rw [hd'eq q hq]
    simpa only [hd0, sub_zero, hquadratic, Real.norm_eq_abs] using
      hdisp q (lt_of_lt_of_le (by simpa using hq) hrD')
  have hcoercive' : ∀ q ∈ Metric.ball 0 r, (c / 2) * ‖q‖ ^ 2 ≤ d' q := by
    intro q hq
    have hnorm : ‖q‖ < Real.sqrt (c / (2 * D)) :=
      lt_of_lt_of_le (by simpa using hq) hrsqrt
    have hqsq : ‖q‖ ^ 2 ≤ c / (2 * D) := by
      nlinarith [Real.sq_sqrt (show 0 ≤ c / (2 * D) by positivity), norm_nonneg q,
        Real.sqrt_nonneg (c / (2 * D))]
    have hDq : D * ‖q‖ ^ 2 ≤ c / 2 := by
      have hh := (le_div_iff₀ (show 0 < 2 * D by positivity)).mp hqsq
      nlinarith
    have hquart := (abs_le.mp (hquartic q hq)).1
    have herr := mul_le_mul_of_nonneg_right hDq (sq_nonneg ‖q‖)
    nlinarith [hcoercive q]
  let C : LocalBandChart F := {
    radius := r
    coercivity := c / 2
    numeratorRemainder := N
    dispersionRemainder := D
    radius_pos := hr
    coercivity_pos := half_pos hc
    numeratorRemainder_nonneg := hN.le
    dispersionRemainder_nonneg := hD.le
    numerator := evenPart B
    dispersion := d'
    edgeNumerator := B 0
    quadraticRoot := L
    numerator_measurable := hBeven.aestronglyMeasurable measurableSet_ball
    dispersion_measurable := hd'm
    dispersion_coercive := fun q hq _ => hcoercive' q hq
    quadratic_coercive := fun q => by
      have hh := hcoercive q
      have hpos := sq_nonneg ‖q‖
      nlinarith
    dispersion_quartic := hquartic
    numerator_quadratic := fun q hq => hnum q (lt_of_lt_of_le (by simpa using hq) hrN') }
  have hbi (ξ : ℝ) (hξ : 0 ≤ ξ) : IntegrableOn (fun q => (d' q + ξ)⁻¹ • B q) (Metric.ball 0 r) :=
    local_bounded_band_integrable B d' (half_pos hc) hξ
      (hBc.aestronglyMeasurable measurableSet_ball) hd'm
      (fun q hq _ => hcoercive' q hq)
      (fun q hq => (hlocal (hq0 q hq)).2.2.2.le)
  refine ⟨C, hrlimit, rfl, rfl, rfl, hd'eq, ?_, ?_⟩
  · intro ξ hξ
    have he : ∀ q ∈ Metric.ball 0 r, d' (-q) = d' q := by
      intro q hq
      rw [hd'eq q hq, hd'eq (-q) (by simpa using hq)]
      exact (hlocal (hq0 q hq)).2.2.1
    change (∫ q in Metric.ball 0 r, (d' q + ξ)⁻¹ • evenPart B q) = _
    rw [← integral_even_numerator volume B d' r ξ he (hbi ξ hξ)]
    apply setIntegral_congr_fun measurableSet_ball
    intro q hq
    dsimp only
    rw [hd'eq q hq]
  · intro ξ hξ
    apply (hbi ξ hξ).congr
    filter_upwards [ae_restrict_mem measurableSet_ball] with q hq
    rw [hd'eq q hq]

end Maxwell.Defect
