import Maxwell.Continuum.FiberL1Analytic
import Maxwell.Continuum.PhysicalFiberL1Variation
import Maxwell.Continuum.CellBandFourierL1

/-! The actual normalized Fourier mode as an ℓ¹-valued analytic function
along any holomorphic parameter curve in the physical momentum chart.
Fourier reconstruction preserves this analyticity in the uniform cell norm. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber FiberNormalization CellBandFourier Set

attribute [local irreducible] normalizedFiberVector physicalFiberVector

def physicalFiberL1 (q : Momentum) : FiberL1.Space := by
  classical
  exact if hq : q ∈ physicalChart then
    ⟨fun ν => physicalFiberVector q ν, memℓp_gen (by
      simpa only [ENNReal.toReal_one, Real.rpow_one] using (physicalFiberVector_fourier_l1 hq).1)⟩
  else 0

theorem physicalFiberL1_apply {q : Momentum} (hq : q ∈ physicalChart) (ν : Alias) :
    physicalFiberL1 q ν = physicalFiberVector q ν := by
  simp only [physicalFiberL1, dite_eq_left hq]

theorem inclusion_physicalFiberL1 {q : Momentum} (hq : q ∈ physicalChart) :
    FiberL1.inclusion (physicalFiberL1 q) = physicalFiberVector q := by
  apply Subtype.ext
  funext ν
  exact physicalFiberL1_apply hq ν

theorem physicalFiberL1_norm (q : Momentum) : ‖physicalFiberL1 q‖ ≤ 32 := by
  by_cases hq : q ∈ physicalChart
  · rw [FiberL1.norm_eq_tsum]
    simp only [physicalFiberL1_apply hq]
    exact (physicalFiberVector_fourier_l1 hq).2
  · simp only [physicalFiberL1, dite_eq_right hq, norm_zero]
    norm_num

theorem physicalFiberL1_curve_analytic {g : ℂ → Momentum} {U : Set ℂ} (hU : IsOpen U)
    (hg : AnalyticOnNhd ℂ g U) (hmap : MapsTo g U physicalChart) :
    AnalyticOnNhd ℂ (fun z => physicalFiberL1 (g z)) U := by
  apply FiberL1.analyticOnNhd_of_inclusion hU (C := 32) (by norm_num)
  · have ha : AnalyticOnNhd ℂ (fun z => physicalFiberVector (g z)) U := by
      intro z hz
      exact AnalyticAt.comp (f := g) (physicalFiberVector_analytic _ (hmap hz)) (hg z hz)
    exact AnalyticOnNhd.congr hU ha (fun z hz => (inclusion_physicalFiberL1 (hmap hz)).symm)
  · intro z _
    exact physicalFiberL1_norm (g z)

theorem physicalPeriodic_curve_analytic {g : ℂ → Momentum} {U : Set ℂ} (hU : IsOpen U)
    (hg : AnalyticOnNhd ℂ g U) (hmap : MapsTo g U physicalChart) :
    AnalyticOnNhd ℂ (fun z => periodicSeries (physicalFiberVector (g z))) U := by
  have ha : AnalyticOnNhd ℂ (fun z => periodicSeriesL1 (physicalFiberL1 (g z))) U := by
    intro z hz
    exact AnalyticAt.comp (f := fun z => physicalFiberL1 (g z)) (periodicSeriesL1.analyticAt _)
      (physicalFiberL1_curve_analytic hU hg hmap z hz)
  apply AnalyticOnNhd.congr hU ha
  intro z hz
  change periodicSeriesL1 (physicalFiberL1 (g z)) = periodicSeries (physicalFiberVector (g z))
  rw [periodicSeriesL1_eq, inclusion_physicalFiberL1 (hmap hz)]

theorem physicalCell_curve_analytic {g : ℂ → Momentum} {U : Set ℂ} (hU : IsOpen U)
    (hg : AnalyticOnNhd ℂ g U) (hmap : MapsTo g U physicalChart) (x : Space) :
    AnalyticOnNhd ℂ (fun z => cellEigenfunction (unscale (g z)) x) U := by
  have ha : AnalyticOnNhd ℂ (fun z => cellEvaluationL1 x (physicalFiberL1 (g z))) U := by
    intro z hz
    exact AnalyticAt.comp (f := fun z => physicalFiberL1 (g z)) ((cellEvaluationL1 x).analyticAt _)
      (physicalFiberL1_curve_analytic hU hg hmap z hz)
  apply AnalyticOnNhd.congr hU ha
  intro z hz
  change cellEvaluationL1 x (physicalFiberL1 (g z)) = cellEigenfunction (unscale (g z)) x
  rw [cellEvaluationL1_eq, inclusion_physicalFiberL1 (hmap hz)]
  simp only [physicalFiberVector, cellEigenfunction]

theorem physicalFiberL1_sub_zero {q : Momentum} (hq : ‖q‖ ≤ analyticRadius / 4) :
    ‖physicalFiberL1 q - physicalFiberL1 0‖ ≤ (128 / analyticRadius) * ‖q‖ := by
  have hsmall : q ∈ physicalChart := by
    intro j
    exact (norm_le_pi_norm q j).trans_lt (hq.trans_lt (by linarith [analyticRadius_pos]))
  have h0 : (0 : Momentum) ∈ physicalChart := by
    intro j
    simpa only [Pi.zero_apply, norm_zero] using analyticRadius_pos
  rw [FiberL1.norm_eq_tsum]
  simpa only [lp.coeFn_sub, Pi.sub_apply, physicalFiberL1_apply hsmall,
    physicalFiberL1_apply h0] using (physicalFiberVector_l1_sub_zero hq).2

theorem physicalPeriodic_sub_zero {q : Momentum} (hq : ‖q‖ ≤ analyticRadius / 4) :
    ‖periodicSeries (physicalFiberVector q) - periodicSeries (physicalFiberVector 0)‖ ≤
      (128 / analyticRadius) * ‖q‖ := by
  have hsmall : q ∈ physicalChart := by
    intro j
    exact (norm_le_pi_norm q j).trans_lt (hq.trans_lt (by linarith [analyticRadius_pos]))
  have h0 : (0 : Momentum) ∈ physicalChart := by
    intro j
    simpa only [Pi.zero_apply, norm_zero] using analyticRadius_pos
  have heq : periodicSeries (physicalFiberVector q) - periodicSeries (physicalFiberVector 0) =
      periodicSeriesL1 (physicalFiberL1 q - physicalFiberL1 0) := by
    rw [map_sub, periodicSeriesL1_eq, periodicSeriesL1_eq,
      inclusion_physicalFiberL1 hsmall, inclusion_physicalFiberL1 h0]
  rw [heq]
  calc
    _ ≤ ‖periodicSeriesL1‖ * ‖physicalFiberL1 q - physicalFiberL1 0‖ :=
      periodicSeriesL1.le_opNorm _
    _ ≤ 1 * ‖physicalFiberL1 q - physicalFiberL1 0‖ :=
      mul_le_mul_of_nonneg_right periodicSeriesL1_norm (norm_nonneg _)
    _ ≤ (128 / analyticRadius) * ‖q‖ := by
      simpa only [one_mul] using physicalFiberL1_sub_zero hq

#print axioms physicalFiberL1_curve_analytic
#print axioms physicalPeriodic_curve_analytic
#print axioms physicalCell_curve_analytic
#print axioms physicalPeriodic_sub_zero

end Maxwell.Continuum.PeriodicBand
