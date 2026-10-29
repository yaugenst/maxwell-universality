import Maxwell.Continuum.PeriodicBandProjectionAnalytic
import Maxwell.Continuum.PeriodicPhysicalBand
import Maxwell.Continuum.CauchyLipschitz

/-! Quantitative variation of the actual normalized full Fourier eigenvector
in physical momentum. The bound follows from Banach-valued holomorphy. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber FiberNormalization Set Metric

attribute [local irreducible] PeriodicPerturbation.perturbation PeriodicPerturbation.finiteK
  CornerBridge.topState RankOneBand.Data.bandRoot scaledBand clusterVector
  fiberVector normalizedFiberVector

def physicalFiberVector (q : Momentum) : FiberSpace := normalizedFiberVector (unscale q)

theorem physicalFiberVector_analytic : AnalyticOnNhd ℂ physicalFiberVector physicalChart := by
  intro q hq
  have hu : AnalyticAt ℂ unscale q :=
    ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := Momentum) (F := Momentum)
      ((backgroundAmplitude : ℂ)⁻¹ • ContinuousLinearMap.id ℂ Momentum) q
  exact AnalyticAt.comp (f := unscale)
    (normalizedFiberVector_analytic _ (unscale_mem_chart hq)) hu

theorem physicalFiberVector_norm_le {q : Momentum} (hq : q ∈ physicalChart) :
    ‖physicalFiberVector q‖ ≤ 2 :=
  (normalizedFiberVector_norm_le (unscale_mem_chart hq)).trans (by norm_num)

theorem bounded_line_physicalChart {t : Momentum} (ht : ∀ j, ‖t j‖ ≤ 1)
    {z : ℂ} (hz : ‖z‖ ≤ analyticRadius / 2) : z • t ∈ physicalChart := by
  intro j
  change ‖z * t j‖ < analyticRadius
  rw [norm_mul]
  have h := mul_le_mul_of_nonneg_left (ht j) (norm_nonneg z)
  nlinarith [analyticRadius_pos]

theorem physicalFiberVector_line_sub {t : Momentum} (ht : ∀ j, ‖t j‖ ≤ 1)
    {z : ℂ} (hz : ‖z‖ ≤ analyticRadius / 4) :
    ‖physicalFiberVector (z • t) - physicalFiberVector 0‖ ≤
      (8 / analyticRadius) * ‖z‖ := by
  let f : ℂ → FiberSpace := fun w => physicalFiberVector (w • t)
  have hf : AnalyticOnNhd ℂ f (closedBall 0 (analyticRadius / 2)) := by
    intro w hw
    have hw' : ‖w‖ ≤ analyticRadius / 2 := by
      simpa only [mem_closedBall, dist_zero_right] using hw
    exact AnalyticAt.comp (f := fun u : ℂ => u • t)
      (physicalFiberVector_analytic _ (bounded_line_physicalChart ht hw'))
      (analyticAt_id.smul analyticAt_const)
  have hB : ∀ w ∈ closedBall (0 : ℂ) (analyticRadius / 2), ‖f w‖ ≤ 2 := by
    intro w hw
    apply physicalFiberVector_norm_le
    apply bounded_line_physicalChart ht
    simpa only [mem_closedBall, dist_zero_right] using hw
  have h := CauchyBounds.bounded_curve_sub_le
    (show 0 < analyticRadius / 2 by linarith [analyticRadius_pos]) (by norm_num : (0 : ℝ) ≤ 2)
    hf hB (c := z) (d := 0)
    (by simpa only [mem_closedBall, dist_zero_right] using (show ‖z‖ ≤ analyticRadius / 2 / 2 by linarith))
    (by simp only [mem_closedBall, dist_self]; linarith [analyticRadius_pos])
  have heq : 2 * (2 : ℝ) / (analyticRadius / 2) = 8 / analyticRadius := by ring
  simpa only [f, zero_smul, sub_zero, heq] using h

theorem physicalFiberVector_sub_zero {q : Momentum} (hq : ‖q‖ ≤ analyticRadius / 4) :
    ‖physicalFiberVector q - physicalFiberVector 0‖ ≤ (8 / analyticRadius) * ‖q‖ := by
  by_cases hq0 : q = 0
  · subst q
    simp
  have hn : 0 < ‖q‖ := norm_pos_iff.mpr hq0
  let t : Momentum := ((‖q‖ : ℝ) : ℂ)⁻¹ • q
  have ht : ∀ j, ‖t j‖ ≤ 1 := by
    intro j
    change ‖((‖q‖ : ℝ) : ℂ)⁻¹ * q j‖ ≤ 1
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn]
    exact (mul_le_mul_of_nonneg_left (norm_le_pi_norm q j) (inv_nonneg.mpr hn.le)).trans_eq
      (inv_mul_cancel₀ hn.ne')
  have hrec : ((‖q‖ : ℝ) : ℂ) • t = q := by
    dsimp only [t]
    rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hn.ne'), one_smul]
  have h := physicalFiberVector_line_sub ht (z := ((‖q‖ : ℝ) : ℂ)) (by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn] using hq)
  simpa only [hrec, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn] using h

end Maxwell.Continuum.PeriodicBand
