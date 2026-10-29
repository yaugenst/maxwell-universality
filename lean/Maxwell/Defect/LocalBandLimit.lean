import Maxwell.Defect.AnalyticLocalChart
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Dominated convergence at the integrable three-dimensional band edge. -/
namespace Maxwell.Defect

open MeasureTheory Filter Topology
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem local_bounded_band_tendsto_zero (B : Momentum → F) (d : Momentum → ℝ)
    {r c M : ℝ} (hc : 0 < c)
    (hBm : AEStronglyMeasurable B (volume.restrict (Metric.ball 0 r)))
    (hdm : Measurable d)
    (hd : ∀ q ∈ Metric.ball 0 r, q ≠ 0 → c * ‖q‖ ^ 2 ≤ d q)
    (hB : ∀ q ∈ Metric.ball 0 r, ‖B q‖ ≤ M)
    (ξ : ℕ → ℝ) (hξ : ∀ n, 0 ≤ ξ n) (hlim : Tendsto ξ atTop (𝓝 0)) :
    Tendsto (fun n => ∫ q in Metric.ball 0 r, (d q + ξ n)⁻¹ • B q)
      atTop (𝓝 (∫ q in Metric.ball 0 r, (d q)⁻¹ • B q)) := by
  apply tendsto_integral_of_dominated_convergence (fun q => M / c * (1 / ‖q‖ ^ 2))
  · intro n
    exact ((hdm.add_const (ξ n)).inv.aestronglyMeasurable).smul hBm
  · exact (inverse_square_integrable_ball r).const_mul (M / c)
  · intro n
    have hne : ∀ᵐ q : Momentum, q ≠ 0 := by simp [ae_iff]
    filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hne] with q hq hq0
    have hr : 0 < ‖q‖ := norm_pos_iff.mpr hq0
    have hdq : 0 < d q + ξ n := by nlinarith [hd q hq hq0, hξ n, sq_pos_of_pos hr]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hdq)]
    calc
      (d q + ξ n)⁻¹ * ‖B q‖ ≤ (c * ‖q‖ ^ 2)⁻¹ * M := by
        apply mul_le_mul
        · apply inv_anti₀ (by positivity)
          linarith [hd q hq hq0, hξ n]
        · exact hB q hq
        · exact norm_nonneg _
        · positivity
      _ = M / c * (1 / ‖q‖ ^ 2) := by field_simp
  · have hne : ∀ᵐ q : Momentum, q ≠ 0 := by simp [ae_iff]
    filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hne] with q hq hq0
    have hdq : 0 < d q := lt_of_lt_of_le
      (mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hq0))) (hd q hq hq0)
    have hden : Tendsto (fun n => d q + ξ n) atTop (𝓝 (d q)) := by
      simpa only [add_zero] using tendsto_const_nhds.add hlim
    exact (hden.inv₀ hdq.ne').smul tendsto_const_nhds

end Maxwell.Defect
