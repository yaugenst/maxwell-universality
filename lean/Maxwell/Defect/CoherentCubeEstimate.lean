import Maxwell.Defect.CoherentCubeProfile
import Maxwell.Defect.Coherence
import Maxwell.Defect.AnalyticLocalChart
import Maxwell.Defect.LocalBandLimit

/-! Quantitative Rayleigh input for the actual scalar-cell cube source. -/
namespace Maxwell.Defect.ScalarDefect

open Spectral Spectral.Lattice Spectral.Bloch MeasureTheory
open Maxwell.Green.PhysicalCompression

theorem coherent_finiteField_norm_sq_le (L : ℕ) (φ : EuclideanSpace ℂ Edge20)
    (center : Torus) :
    ‖finiteField (edgeEmbedding (cube L)) (coherentLatticeCoefficients L φ center)‖ ^ 2 ≤
      cubeMass L φ := by
  rw [coherent_finiteField]
  have h := defectInjection_norm_apply_le (edgeEmbedding (cube L)) (coordinateWeight (cube L))
    (fun i => le_trans (by norm_num) (coordinateWeight_bounds (cube L) i).1)
    (fun i => (coordinateWeight_bounds (cube L) i).2)
    (coherentCoordinates L φ (fun n => UnitAddTorus.mFourier n center))
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [coherentCoordinates_norm_sq _ _ _ (fun n => mFourier_apply_norm n center)] at hs
  exact hs

theorem coherentAmplitude_lower (L : ℕ) (hL : 8 ≤ L)
    (φ φ₀ : EuclideanSpace ℂ Edge20) (hφ₀ : ‖φ₀‖ = 1)
    (q : Momentum) {r C : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hqr : ‖q‖ ≤ r / L) (hrsmall : r ≤ 1 / 64) (hrC : r ≤ 1 / (64 * (1 + C)))
    (hvariation : ‖φ - φ₀‖ ≤ C * ‖q‖) :
    cubeMass L φ₀ / 2 ≤ ‖coherentAmplitude L φ φ₀ q‖ := by
  exact coherent_overlap_lower (by exact_mod_cast hL)
    (cubeMass_bounds L (by omega) φ₀ hφ₀).1 (norm_nonneg _) hr hC hqr hrsmall hrC
    (coherentAmplitude_error L (by omega) φ φ₀ hφ₀ q C hC hvariation)

theorem coherentAmplitude_norm_le (L : ℕ) (φ φ₀ : EuclideanSpace ℂ Edge20)
    (hφ : ‖φ‖ = 1) (hφ₀ : ‖φ₀‖ = 1) (q : Momentum) :
    ‖coherentAmplitude L φ φ₀ q‖ ≤ (supportPeriods L).card := by
  unfold coherentAmplitude
  apply (norm_inner_le_norm _ _).trans
  rw [hφ, one_mul]
  simpa only [Fintype.card_coe, mul_one, Complex.ofReal_neg] using
    finite_fourier_source_norm
      (fun n : ↥(supportPeriods L) => -(inner ℝ q (periodVector n)))
      (fun n : ↥(supportPeriods L) => cellSource L φ₀ n)
      (fun n => cellSource_norm_le_one L φ₀ hφ₀ n)

theorem coherentAmplitude_continuousOn (L : ℕ) (φ₀ : EuclideanSpace ℂ Edge20)
    (φ : Momentum → EuclideanSpace ℂ Edge20) (s : Set Momentum)
    (hφ : ContinuousOn φ s) : ContinuousOn (fun q => coherentAmplitude L (φ q) φ₀ q) s := by
  unfold coherentAmplitude
  apply hφ.inner
  apply Continuous.continuousOn
  apply continuous_finsetSum
  intro n _
  fun_prop

/-- The singular selected-band Rayleigh integrand is genuinely integrable
at the edge; the inverse-square majorant is integrable in three dimensions. -/
theorem coherent_pole_integrable (L : ℕ) (φ₀ : EuclideanSpace ℂ Edge20)
    (hφ₀ : ‖φ₀‖ = 1) (φ : Momentum → EuclideanSpace ℂ Edge20)
    (d : Momentum → ℝ) {r c : ℝ} (hc : 0 < c)
    (hφ : ContinuousOn φ (Metric.ball 0 r))
    (hunit : ∀ q ∈ Metric.ball 0 r, ‖φ q‖ = 1)
    (hd : Measurable d)
    (hlower : ∀ q ∈ Metric.ball 0 r, q ≠ 0 → c * ‖q‖ ^ 2 ≤ d q) :
    IntegrableOn (fun q => ‖coherentAmplitude L (φ q) φ₀ q‖ ^ 2 / d q)
      (Metric.ball 0 r) := by
  have hcont := (coherentAmplitude_continuousOn L φ₀ φ _ hφ).norm.pow 2
  have hm : AEStronglyMeasurable
      (fun q => ‖coherentAmplitude L (φ q) φ₀ q‖ ^ 2)
      (volume.restrict (Metric.ball 0 r)) :=
    hcont.aestronglyMeasurable measurableSet_ball
  have hi := local_bounded_band_integrable
    (fun q => ‖coherentAmplitude L (φ q) φ₀ q‖ ^ 2) d
    (M := ((supportPeriods L).card : ℝ) ^ 2) hc (show (0 : ℝ) ≤ 0 by rfl) hm hd hlower
    (fun q hq => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (coherentAmplitude_norm_le L (φ q) φ₀
        (hunit q hq) hφ₀ q) 2)
  simpa only [add_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using hi

/-- Exact quadratic cube growth of the coherent selected-band integral. -/
theorem coherent_cube_pole_lower (L : ℕ) (hL : 8 ≤ L)
    (φ₀ : EuclideanSpace ℂ Edge20) (hφ₀ : ‖φ₀‖ = 1)
    (φ : Momentum → EuclideanSpace ℂ Edge20) (d : Momentum → ℝ)
    {r c dmax C : ℝ} (hr : 0 < r) (hc : 0 < c) (hdmax : 0 < dmax) (hC : 0 ≤ C)
    (hrsmall : r ≤ 1 / 64) (hrC : r ≤ 1 / (64 * (1 + C)))
    (hφ : ContinuousOn φ (Metric.ball 0 (r / L)))
    (hunit : ∀ q ∈ Metric.ball 0 (r / L), ‖φ q‖ = 1)
    (hvariation : ∀ q ∈ Metric.ball 0 (r / L), ‖φ q - φ₀‖ ≤ C * ‖q‖)
    (hd : Measurable d)
    (hlower : ∀ q ∈ Metric.ball 0 (r / L), q ≠ 0 → c * ‖q‖ ^ 2 ≤ d q)
    (hupper : ∀ q ∈ Metric.ball 0 (r / L), d q ≤ dmax * ‖q‖ ^ 2) :
    (cubeMass L φ₀) ^ 2 * r / (8 * Real.pi ^ 2 * dmax * L) ≤
      (∫ q in Metric.ball 0 (r / L), ‖coherentAmplitude L (φ q) φ₀ q‖ ^ 2 / d q) /
        (2 * Real.pi) ^ 3 := by
  have hLpos : 0 < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have ha := (cubeMass_bounds L (by omega) φ₀ hφ₀).1
  have h := coherent_ball_integral_lower (fun q => coherentAmplitude L (φ q) φ₀ q) d
    ((pow_nonneg hLpos.le 3).trans ha) (div_pos hr hLpos) hdmax
    (coherent_pole_integrable L φ₀ hφ₀ φ d hc hφ hunit hd hlower)
    (fun q hq _ => coherentAmplitude_lower L hL (φ q) φ₀ hφ₀ q hr.le hC
      (le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hq))
      hrsmall hrC (hvariation q hq))
    (fun q hq hq0 => ⟨lt_of_lt_of_le (mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hq0)))
      (hlower q hq hq0), hupper q hq⟩)
  convert h using 1
  ring

theorem coherent_shifted_pole_integrable (L : ℕ) (φ₀ : EuclideanSpace ℂ Edge20)
    (hφ₀ : ‖φ₀‖ = 1) (φ : Momentum → EuclideanSpace ℂ Edge20)
    (d : Momentum → ℝ) {r c ξ : ℝ} (hc : 0 < c) (hξ : 0 ≤ ξ)
    (hφ : ContinuousOn φ (Metric.ball 0 r))
    (hunit : ∀ q ∈ Metric.ball 0 r, ‖φ q‖ = 1) (hd : Measurable d)
    (hlower : ∀ q ∈ Metric.ball 0 r, q ≠ 0 → c * ‖q‖ ^ 2 ≤ d q) :
    IntegrableOn (fun q => ‖coherentAmplitude L (φ q) φ₀ q‖ ^ 2 / (d q + ξ))
      (Metric.ball 0 r) := by
  have hcont := (coherentAmplitude_continuousOn L φ₀ φ _ hφ).norm.pow 2
  have hm : AEStronglyMeasurable
      (fun q => ‖coherentAmplitude L (φ q) φ₀ q‖ ^ 2)
      (volume.restrict (Metric.ball 0 r)) :=
    hcont.aestronglyMeasurable measurableSet_ball
  have hi := local_bounded_band_integrable
    (fun q => ‖coherentAmplitude L (φ q) φ₀ q‖ ^ 2) d
    (M := ((supportPeriods L).card : ℝ) ^ 2) hc hξ hm hd hlower
    (fun q hq => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (coherentAmplitude_norm_le L (φ q) φ₀
        (hunit q hq) hφ₀ q) 2)
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using hi

theorem coherent_pole_tendsto_zero (L : ℕ) (φ₀ : EuclideanSpace ℂ Edge20)
    (hφ₀ : ‖φ₀‖ = 1) (φ : Momentum → EuclideanSpace ℂ Edge20)
    (d : Momentum → ℝ) {r c : ℝ} (hc : 0 < c)
    (hφ : ContinuousOn φ (Metric.ball 0 r))
    (hunit : ∀ q ∈ Metric.ball 0 r, ‖φ q‖ = 1) (hd : Measurable d)
    (hlower : ∀ q ∈ Metric.ball 0 r, q ≠ 0 → c * ‖q‖ ^ 2 ≤ d q)
    (ξ : ℕ → ℝ) (hξ : ∀ n, 0 ≤ ξ n) (hlim : Filter.Tendsto ξ Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => ∫ q in Metric.ball 0 r, ‖coherentAmplitude L (φ q) φ₀ q‖ ^ 2 / (d q + ξ n))
      Filter.atTop (nhds (∫ q in Metric.ball 0 r, ‖coherentAmplitude L (φ q) φ₀ q‖ ^ 2 / d q)) := by
  have hcont := (coherentAmplitude_continuousOn L φ₀ φ _ hφ).norm.pow 2
  have hm : AEStronglyMeasurable
      (fun q => ‖coherentAmplitude L (φ q) φ₀ q‖ ^ 2)
      (volume.restrict (Metric.ball 0 r)) :=
    hcont.aestronglyMeasurable measurableSet_ball
  have hi := local_bounded_band_tendsto_zero
    (fun q => ‖coherentAmplitude L (φ q) φ₀ q‖ ^ 2) d
    (M := ((supportPeriods L).card : ℝ) ^ 2) hc hm hd hlower
    (fun q hq => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (coherentAmplitude_norm_le L (φ q) φ₀
        (hunit q hq) hφ₀ q) 2) ξ hξ hlim
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using hi

end Maxwell.Defect.ScalarDefect
