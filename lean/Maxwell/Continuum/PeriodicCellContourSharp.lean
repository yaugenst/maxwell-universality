import Maxwell.Continuum.PeriodicCellContour
import Maxwell.Continuum.PeriodicTubeTransition

/-! The transition-shell estimate removes every inverse power of the
well scale from the contour error for the actual cell symbol. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.CellGauge

open Complex FreeFiber PeriodicBand Auxiliary MasterConstants Set

theorem fullCellSymbol_contour_bound_sharp {L z σ : ℝ} (hL : Ls ≤ L)
    (D : Calibration L⁻¹ z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4/64) (R : Space) :
    ‖OperatorFourier.angularFourier
      (fun q => (Well.chi smallRadius q : ℂ) • fullCellSymbol z σ (realMomentumMap q)) (-R)‖ ≤
      (2 : ℝ)^63*L^2*Real.exp (-(99/100 : ℝ)*L⁻¹*dualHessianDistance R.ofLp) +
        (2 : ℝ)^245*Real.exp (-cs*L) := by
  let β := cellContourShift L R
  have hβ : ‖β‖ ≤ L⁻¹ := cellContourShift_norm_le hL R
  have hphase : 0 ≤ inner ℝ β R := by
    rw [cellContourShift_phase]
    exact mul_nonneg (mul_nonneg (by norm_num) D.h_pos.le) (dualHessianDistance_nonneg _)
  have hh : L⁻¹ ≤ 1/(2 : ℝ)^1024 := inverse_length_le_1024 hL
  have hqchart {q : Space} (hq : ‖q‖ ≤ 4*smallRadius) :
      ‖realMomentum q.ofLp‖ ≤ 4*smallRadius := (realMomentumMap_norm_le q).trans hq
  have ha : ∀ s ∈ Icc (0 : ℝ) 1, ∀ q, ‖q‖ ≤ 4*smallRadius →
      AnalyticAt ℂ (fullCellSymbol z σ) (AlmostAnalytic.shiftedMomentum q β s) := by
    intro s hs q hq
    rw [cellContourShift_momentum]
    exact optimalTubeShift_cell_analytic D hh hσ0 hσ q.ofLp R.ofLp (hqchart hq) hs
  have hb : ∀ q, ‖q‖ ≤ 4*smallRadius →
      ‖fullCellSymbol z σ (AlmostAnalytic.shiftedMomentum q β 1)‖ ≤ (2 : ℝ)^14*L^2 := by
    intro q hq
    rw [cellContourShift_momentum]
    simpa only [inv_pow, inv_inv] using
      optimalTubeShift_cell_norm_le D hh hσ0 hσ q.ofLp R.ofLp (hqchart hq)
        (s := 1) ⟨by norm_num, le_rfl⟩
  have hshell : ∀ s ∈ Icc (0 : ℝ) 1, ∀ q : Space, smallRadius ≤ ‖q‖ →
      ‖q‖ ≤ 4*smallRadius →
        ‖fullCellSymbol z σ (AlmostAnalytic.shiftedMomentum q β s)‖ ≤ (2 : ℝ)^196 := by
    intro s hs q hq0 hq
    rw [cellContourShift_momentum]
    apply transition_cell_norm_le D hh hσ0 hσ q.ofLp _ hq0 (hqchart hq)
    exact (tube_segment_energy _ (optimalTubeShift_energy L⁻¹ R.ofLp) hs).trans
      (mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg L⁻¹))
  have he := AlmostAnalytic.cutoff_fourier_bound hL hβ R hphase (fullCellSymbol z σ)
    (show 0 ≤ (2 : ℝ)^14*L^2 by positivity) (show 0 ≤ (2 : ℝ)^196 by positivity) ha hb hshell
  apply he.trans_eq
  rw [cellContourShift_phase]
  have heq : -((99/100 : ℝ)*L⁻¹*dualHessianDistance R.ofLp) =
      -(99/100 : ℝ)*L⁻¹*dualHessianDistance R.ofLp := by ring
  rw [heq]
  ring

#print axioms fullCellSymbol_contour_bound_sharp

end Maxwell.Continuum.CellGauge
