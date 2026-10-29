import Maxwell.Continuum.FiberL1Cauchy
import Maxwell.Continuum.PhysicalFiberVariation
import Maxwell.Continuum.CellBandFourierReference

/-! Complex-momentum variation of every Fourier alias of the actual
normalized cell mode. The finite-functional Cauchy estimate has a constant
independent of the number of aliases. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber FiberNormalization Set Metric CellBandFourier

attribute [local irreducible] PeriodicPerturbation.perturbation PeriodicPerturbation.finiteK
  CornerBridge.topState RankOneBand.Data.bandRoot scaledBand clusterVector
  fiberVector normalizedFiberVector physicalFiberVector

theorem physicalFiberVector_fourier_l1 {q : Momentum} (hq : q ∈ physicalChart) :
    Summable (fun ν => ‖physicalFiberVector q ν‖) ∧ ∑' ν, ‖physicalFiberVector q ν‖ ≤ 32 := by
  simp only [physicalFiberVector]
  exact normalizedFiberVector_fourier_l1 (unscale_mem_chart hq)

theorem physicalFiberVector_line_l1_sub {t : Momentum} (ht : ∀ j, ‖t j‖ ≤ 1)
    {z : ℂ} (hz : ‖z‖ ≤ analyticRadius / 4) :
    Summable (fun ν => ‖physicalFiberVector (z • t) ν - physicalFiberVector 0 ν‖) ∧
      (∑' ν, ‖physicalFiberVector (z • t) ν - physicalFiberVector 0 ν‖) ≤
        (128 / analyticRadius) * ‖z‖ := by
  let f : ℂ → FiberSpace := fun w => physicalFiberVector (w • t)
  have hf : AnalyticOnNhd ℂ f (closedBall 0 (analyticRadius / 2)) := by
    intro w hw
    have hw' : ‖w‖ ≤ analyticRadius / 2 := by
      simpa only [mem_closedBall, dist_zero_right] using hw
    exact AnalyticAt.comp (f := fun u : ℂ => u • t)
      (physicalFiberVector_analytic _ (bounded_line_physicalChart ht hw'))
      (analyticAt_id.smul analyticAt_const)
  have hB : ∀ w ∈ closedBall (0 : ℂ) (analyticRadius / 2),
      Summable (fun ν => ‖f w ν‖) ∧ ∑' ν, ‖f w ν‖ ≤ 32 := by
    intro w hw
    apply physicalFiberVector_fourier_l1
    apply bounded_line_physicalChart ht
    simpa only [mem_closedBall, dist_zero_right] using hw
  have h := FiberL1.analytic_curve_l1_sub_le
    (show 0 < analyticRadius / 2 by linarith [analyticRadius_pos]) (by norm_num : (0 : ℝ) ≤ 32)
    hf hB (c := z) (d := 0)
    (by simpa only [mem_closedBall, dist_zero_right] using
      (show ‖z‖ ≤ analyticRadius / 2 / 2 by linarith))
    (by simp only [mem_closedBall, dist_self]; linarith [analyticRadius_pos])
  have heq : 2 * (32 : ℝ) / (analyticRadius / 2) = 128 / analyticRadius := by ring
  simpa only [f, zero_smul, sub_zero, heq] using h

theorem physicalFiberVector_l1_sub_zero {q : Momentum} (hq : ‖q‖ ≤ analyticRadius / 4) :
    Summable (fun ν => ‖physicalFiberVector q ν - physicalFiberVector 0 ν‖) ∧
      (∑' ν, ‖physicalFiberVector q ν - physicalFiberVector 0 ν‖) ≤
        (128 / analyticRadius) * ‖q‖ := by
  by_cases hq0 : q = 0
  · subst q
    simp only [sub_self, norm_zero, summable_zero, tsum_zero, mul_zero, le_refl, and_self]
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
  have h := physicalFiberVector_line_l1_sub ht (z := ((‖q‖ : ℝ) : ℂ)) (by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn] using hq)
  simpa only [hrec, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn] using h

theorem physicalFiberVector_l1_sub_zero_paper {q : Momentum} (hq : ‖q‖ ≤ analyticRadius / 4) :
    (∑' ν, ‖physicalFiberVector q ν - physicalFiberVector 0 ν‖) ≤
      ((2 : ℝ)^12 / analyticRadius) * ‖q‖ := by
  apply (physicalFiberVector_l1_sub_zero hq).2.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg q)
  exact div_le_div_of_nonneg_right (by norm_num) analyticRadius_pos.le

theorem physicalCell_sub_zero {q : Momentum} (hq : ‖q‖ ≤ analyticRadius / 4) (x : Space) :
    ‖cellEigenfunction (unscale q) x - cellEigenfunction 0 x‖ ≤
      (128 / analyticRadius) * ‖q‖ := by
  have hsmall : q ∈ physicalChart := by
    intro j
    exact (norm_le_pi_norm q j).trans_lt (hq.trans_lt (by linarith [analyticRadius_pos]))
  have h0 : (0 : Momentum) ∈ physicalChart := by
    intro j
    simpa only [Pi.zero_apply, norm_zero] using analyticRadius_pos
  have hd := physicalFiberVector_l1_sub_zero hq
  have hs : Summable (fun ν => ‖(physicalFiberVector q - physicalFiberVector 0) ν‖) := hd.1
  have heq : cellEigenfunction (unscale q) x - cellEigenfunction 0 x =
      Complex.I • antiperiodicField (physicalFiberVector q - physicalFiberVector 0) x := by
    rw [cellEigenfunction, cellEigenfunction, ← smul_sub]
    have hz : unscale (0 : Momentum) = 0 := by simp only [unscale, smul_zero]
    rw [antiperiodicField_sub _ _ (physicalFiberVector_fourier_l1 hsmall).1
      (physicalFiberVector_fourier_l1 h0).1]
    rw [physicalFiberVector, physicalFiberVector, hz]
  rw [heq, norm_smul, Complex.norm_I, one_mul]
  exact (antiperiodicField_norm_le _ hs x).trans hd.2

#print axioms physicalFiberVector_l1_sub_zero
#print axioms physicalCell_sub_zero

end Maxwell.Continuum.PeriodicBand
