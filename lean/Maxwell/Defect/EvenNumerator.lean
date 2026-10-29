import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Tactic.Module

/-! Even symmetrization removes the first-order numerator term and the
odd dispersion terms. The quadratic and quartic remainder bounds are
proved from actual convergent analytic power series. -/
namespace Maxwell.Defect
open Filter Topology MeasureTheory
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def evenPart (f : E → F) (q : E) : F :=
  (1 / 2 : ℝ) • (f q + f (-q))

theorem powerSeries_term_neg (p : FormalMultilinearSeries ℝ E F) (n : ℕ) (q : E) :
    p n (fun _ => -q) = (-1 : ℝ) ^ n • p n (fun _ => q) := by
  simpa using (p n).map_smul_univ (fun _ => (-1 : ℝ)) (fun _ => q)

theorem evenPart_partialSum_two (p : FormalMultilinearSeries ℝ E F) (q : E) :
    evenPart (p.partialSum 2) q = p 0 (fun _ => q) := by
  simp only [evenPart, FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, powerSeries_term_neg]
  norm_num
  module

theorem evenPart_partialSum_four (p : FormalMultilinearSeries ℝ E F) (q : E) :
    evenPart (p.partialSum 4) q = p 0 (fun _ => q) + p 2 (fun _ => q) := by
  simp only [evenPart, FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, powerSeries_term_neg]
  norm_num
  module

/-- Symmetrization preserves a Taylor remainder bound of any chosen order. -/
theorem analytic_evenPart_remainder (f : E → F) (p : FormalMultilinearSeries ℝ E F)
    (hp : HasFPowerSeriesAt f p 0) (n : ℕ) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ q : E, ‖q‖ < r →
      ‖evenPart f q - evenPart (p.partialSum n) q‖ ≤ C * ‖q‖ ^ n := by
  obtain ⟨C, hC, hbound⟩ := (hp.isBigO_sub_partialSum_pow n).exists_pos
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hbound.bound
  refine ⟨C, r, hC, hr, ?_⟩
  intro q hq
  have hpos := hball (y := q) (by simpa using hq)
  have hneg := hball (y := -q) (by simpa using hq)
  simp only [zero_add, norm_neg, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (norm_nonneg q) n)] at hpos hneg
  have hid : evenPart f q - evenPart (p.partialSum n) q = (1 / 2 : ℝ) •
      ((f q - p.partialSum n q) + (f (-q) - p.partialSum n (-q))) := by
    simp only [evenPart, smul_add, smul_sub]
    abel
  rw [hid, norm_smul]
  norm_num only [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have hh := (norm_add_le _ _).trans (add_le_add hpos hneg)
  nlinarith

/-- The actual even part of an analytic numerator has a quadratic
remainder around its constant value. -/
theorem analytic_evenPart_quadratic (f : E → F) (hf : AnalyticAt ℝ f 0) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ q : E, ‖q‖ < r →
      ‖evenPart f q - f 0‖ ≤ C * ‖q‖ ^ 2 := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨C, r, hC, hr, hb⟩ := analytic_evenPart_remainder f p hp 2
  refine ⟨C, r, hC, hr, ?_⟩
  intro q hq
  simpa only [evenPart_partialSum_two, hp.coeff_zero] using hb q hq

/-- The even analytic dispersion has a quartic remainder after its
constant and quadratic homogeneous terms. -/
theorem analytic_evenPart_quartic (f : E → F) (p : FormalMultilinearSeries ℝ E F)
    (hp : HasFPowerSeriesAt f p 0) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ q : E, ‖q‖ < r →
      ‖evenPart f q - f 0 - p 2 (fun _ => q)‖ ≤ C * ‖q‖ ^ 4 := by
  obtain ⟨C, r, hC, hr, hb⟩ := analytic_evenPart_remainder f p hp 4
  refine ⟨C, r, hC, hr, ?_⟩
  intro q hq
  simpa only [evenPart_partialSum_four, hp.coeff_zero, sub_add_eq_sub_sub] using hb q hq

/-- For a locally even analytic dispersion, the actual dispersion itself
has the quartic remainder required by the edge integral. -/
theorem analytic_even_quartic (f : E → F) (p : FormalMultilinearSeries ℝ E F)
    (hp : HasFPowerSeriesAt f p 0) (heven : ∀ᶠ q in 𝓝 (0 : E), f (-q) = f q) :
    ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ q : E, ‖q‖ < r →
      ‖f q - f 0 - p 2 (fun _ => q)‖ ≤ C * ‖q‖ ^ 4 := by
  obtain ⟨C, r, hC, hr, hbound⟩ := analytic_evenPart_quartic f p hp
  obtain ⟨r', hr', he⟩ := Metric.eventually_nhds_iff.mp heven
  refine ⟨C, min r r', hC, lt_min hr hr', ?_⟩
  intro q hq
  have hneg := he (y := q) (by simpa using lt_of_lt_of_le hq (min_le_right r r'))
  have hev : evenPart f q = f q := by
    simp only [evenPart, hneg, smul_add]
    module
  simpa only [hev] using hbound q (lt_of_lt_of_le hq (min_le_left r r'))

omit [NormedSpace ℝ E]

section Integration
variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsNegInvariant]

omit [NormedSpace ℝ F] [MeasurableSpace E] [BorelSpace E] in
private theorem ball_indicator_neg (g : E → F) (r : ℝ) :
    (Metric.ball (0 : E) r).indicator (fun q => g (-q)) =
      fun q => (Metric.ball (0 : E) r).indicator g (-q) := by
  funext q
  have hmem : -q ∈ Metric.ball (0 : E) r ↔ q ∈ Metric.ball (0 : E) r := by simp
  by_cases hq : q ∈ Metric.ball (0 : E) r
  · simp [hq, hmem.mpr hq]
  · have hn : -q ∉ Metric.ball (0 : E) r := fun h => hq (hmem.mp h)
    simp [hq, hn]

theorem integral_ball_neg (g : E → F) (r : ℝ) :
    (∫ q in Metric.ball (0 : E) r, g (-q) ∂μ) = ∫ q in Metric.ball (0 : E) r, g q ∂μ := by
  rw [← integral_indicator measurableSet_ball, ball_indicator_neg,
    integral_neg_eq_self, integral_indicator measurableSet_ball]

omit [NormedSpace ℝ F] in
theorem integrableOn_ball_neg (g : E → F) (r : ℝ)
    (hg : IntegrableOn g (Metric.ball (0 : E) r) μ) :
    IntegrableOn (fun q => g (-q)) (Metric.ball (0 : E) r) μ := by
  apply (integrable_indicator_iff measurableSet_ball).mp
  rw [ball_indicator_neg]
  exact ((integrable_indicator_iff measurableSet_ball).mpr hg).comp_neg

/-- Even symmetrization leaves the actual local integral unchanged. -/
theorem integral_ball_evenPart (g : E → F) (r : ℝ)
    (hg : IntegrableOn g (Metric.ball (0 : E) r) μ) :
    (∫ q in Metric.ball (0 : E) r, evenPart g q ∂μ) =
      ∫ q in Metric.ball (0 : E) r, g q ∂μ := by
  unfold evenPart
  rw [integral_smul, integral_add hg (integrableOn_ball_neg μ g r hg), integral_ball_neg]
  module

/-- For an even denominator, the selected-band numerator can be replaced
by its actual even part inside the local resolvent integral. -/
theorem integral_even_numerator (B : E → F) (d : E → ℝ) (r ξ : ℝ)
    (hd : ∀ q ∈ Metric.ball (0 : E) r, d (-q) = d q)
    (hint : IntegrableOn (fun q => (d q + ξ)⁻¹ • B q) (Metric.ball (0 : E) r) μ) :
    (∫ q in Metric.ball (0 : E) r, (d q + ξ)⁻¹ • B q ∂μ) =
      ∫ q in Metric.ball (0 : E) r, (d q + ξ)⁻¹ • evenPart B q ∂μ := by
  rw [← integral_ball_evenPart μ (fun q => (d q + ξ)⁻¹ • B q) r hint]
  apply setIntegral_congr_fun measurableSet_ball
  intro q hq
  simp only [evenPart, hd q hq, smul_add, smul_smul]
  module

end Integration
end Maxwell.Defect
