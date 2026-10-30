import Maxwell.Continuum.DerivativeCellKernel
import Maxwell.Continuum.PeriodicCellContour

/-! The nonsingular contour estimate for the actual product inverse,
using one cutoff and the literal dielectric derivative between inverses. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.CellGauge

open Complex FreeFiber PeriodicBand Auxiliary MasterConstants MeasureTheory Set Metric

local instance derivativeContourCellMapRealSpace : NormedSpace ℝ CellMap := NormedSpace.complexToReal

theorem derivativeCellSymbol_contour_bound {L z σ : ℝ} (hL : Ls ≤ L)
    (D : Calibration L⁻¹ z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4/64) (j : Fin 3) (R : Space) :
    ‖OperatorFourier.angularFourier (cutoffDerivativeCellSymbol z σ j) (-R)‖ ≤
      (2 : ℝ)^81 * L^4 *
        (Real.exp (-(99/100 : ℝ)*L⁻¹*dualHessianDistance R.ofLp) + Real.exp (-cs*L)) := by
  let β := cellContourShift L R
  have hβ : ‖β‖ ≤ L⁻¹ := cellContourShift_norm_le hL R
  have hphase : 0 ≤ inner ℝ β R := by
    rw [cellContourShift_phase]
    exact mul_nonneg (mul_nonneg (by norm_num) D.h_pos.le) (dualHessianDistance_nonneg _)
  have hh : L⁻¹ ≤ 1/(2 : ℝ)^1024 := inverse_length_le_1024 hL
  have hqchart {q : Space} (hq : ‖q‖ ≤ 4*smallRadius) :
      ‖realMomentum q.ofLp‖ ≤ 4*smallRadius := (realMomentumMap_norm_le q).trans hq
  have ha : ∀ s ∈ Icc (0 : ℝ) 1, ∀ q, ‖q‖ ≤ 4*smallRadius →
      AnalyticAt ℂ (derivativeCellSymbol z σ j) (AlmostAnalytic.shiftedMomentum q β s) := by
    intro s hs q hq
    rw [cellContourShift_momentum]
    exact derivativeCellSymbol_tube_analyticAt D hh hσ0 hσ j q.ofLp _ (hqchart hq)
      (tube_segment_energy _ (optimalTubeShift_energy L⁻¹ R.ofLp) hs)
  have hb : ∀ s ∈ Icc (0 : ℝ) 1, ∀ q, ‖q‖ ≤ 4*smallRadius →
      ‖derivativeCellSymbol z σ j (AlmostAnalytic.shiftedMomentum q β s)‖ ≤ (2 : ℝ)^32*L^4 := by
    intro s hs q hq
    rw [cellContourShift_momentum]
    simpa only [inv_pow, inv_inv] using
      derivativeCellSymbol_tube_norm_le D hh hσ0 hσ j q.ofLp _ (hqchart hq)
        (tube_segment_energy _ (optimalTubeShift_energy L⁻¹ R.ofLp) hs)
  have he := AlmostAnalytic.cutoff_fourier_bound hL hβ R hphase (derivativeCellSymbol z σ j)
    (show 0 ≤ (2 : ℝ)^32*L^4 by positivity) (show 0 ≤ (2 : ℝ)^32*L^4 by positivity)
    ha (hb 1 ⟨by norm_num, le_rfl⟩) (fun s hs q _ hq => hb s hs q hq)
  apply he.trans_eq
  rw [cellContourShift_phase]
  have heq : -((99/100 : ℝ)*L⁻¹*dualHessianDistance R.ofLp) =
      -(99/100 : ℝ)*L⁻¹*dualHessianDistance R.ofLp := by ring
  rw [heq]
  ring

theorem derivativeResolventSpatialBlock_exponential {L z σ : ℝ} (hL : Ls ≤ L)
    (D : Calibration L⁻¹ z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4/64)
    (j : Fin 3) (a b : Bloch.Alias) :
    ‖derivativeResolventSpatialBlock D hσ0 hσ j a b‖ ≤ (2 : ℝ)^87 * L^4 *
      (Real.exp (-(99/100 : ℝ) * L⁻¹ *
        dualHessianDistance (latticeShift a - latticeShift b).ofLp) + Real.exp (-cs*L)) := by
  have hc := derivativeCellSymbol_contour_bound hL D hσ0 hσ j
    (latticeShift a - latticeShift b)
  rw [neg_sub] at hc
  apply (derivativeResolventSpatialBlock_norm_le_kernel D (inverse_length_le_1024 hL) hσ0 hσ j a b).trans
  apply (mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 64)).trans_eq
  ring

#print axioms derivativeCellSymbol_contour_bound
#print axioms derivativeResolventSpatialBlock_exponential

end Maxwell.Continuum.CellGauge
