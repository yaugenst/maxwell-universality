import Maxwell.Continuum.AlmostAnalyticFourierZero
import Maxwell.Continuum.PeriodicTubeShift

/-! The contour estimate instantiated with the actual complete Maxwell
fiber inverse and its literal within-cell gauge. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.CellGauge

open Complex FreeFiber PeriodicBand Auxiliary MasterConstants MeasureTheory Set Metric

local instance contourCellMapRealSpace : NormedSpace ℝ CellMap := NormedSpace.complexToReal

def cellContourShift (L : ℝ) (R : Space) : Space :=
  WithLp.toLp 2 (optimalTubeShift L⁻¹ R.ofLp)

theorem cellContourShift_momentum (L : ℝ) (R q : Space) (s : ℝ) :
    AlmostAnalytic.shiftedMomentum q (cellContourShift L R) s =
      PeriodicBand.shiftedMomentum q.ofLp (s • optimalTubeShift L⁻¹ R.ofLp) := by
  funext j
  simp only [AlmostAnalytic.shiftedMomentum, realMomentumMap,
    ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply, PiLp.proj_apply,
    Complex.ofRealCLM_apply, PeriodicBand.shiftedMomentum, realMomentum,
    cellContourShift, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  ring

theorem cellContourShift_phase (L : ℝ) (R : Space) :
    inner ℝ (cellContourShift L R) R = (99/100 : ℝ)*L⁻¹*dualHessianDistance R.ofLp := by
  change (∑ j : Fin 3, R j * cellContourShift L R j) = _
  have he := optimalTubeShift_phase L⁻¹ R.ofLp
  rw [dotProduct_comm] at he
  exact he

theorem cellContourShift_norm_le {L : ℝ} (hL : Ls ≤ L) (R : Space) :
    ‖cellContourShift L R‖ ≤ L⁻¹ := by
  have hp := (length_pos hL).le
  exact (optimalTubeShift_norm_le (inv_nonneg.mpr hp) R.ofLp).trans
    (mul_le_of_le_one_left (inv_nonneg.mpr hp) (by norm_num))

theorem fullCellSymbol_contour_bound {L z σ : ℝ} (hL : Ls ≤ L)
    (D : Calibration L⁻¹ z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4/64) (R : Space) :
    ‖OperatorFourier.angularFourier
      (fun q => (Well.chi smallRadius q : ℂ) • fullCellSymbol z σ (realMomentumMap q)) (-R)‖ ≤
      (2 : ℝ)^63 * L^2 *
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
      AnalyticAt ℂ (fullCellSymbol z σ) (AlmostAnalytic.shiftedMomentum q β s) := by
    intro s hs q hq
    rw [cellContourShift_momentum]
    exact optimalTubeShift_cell_analytic D hh hσ0 hσ q.ofLp R.ofLp (hqchart hq) hs
  have hb : ∀ s ∈ Icc (0 : ℝ) 1, ∀ q, ‖q‖ ≤ 4*smallRadius →
      ‖fullCellSymbol z σ (AlmostAnalytic.shiftedMomentum q β s)‖ ≤ (2 : ℝ)^14*L^2 := by
    intro s hs q hq
    rw [cellContourShift_momentum]
    simpa only [inv_pow, inv_inv] using
      optimalTubeShift_cell_norm_le D hh hσ0 hσ q.ofLp R.ofLp (hqchart hq) hs
  have he := AlmostAnalytic.cutoff_fourier_bound hL hβ R hphase (fullCellSymbol z σ)
    (show 0 ≤ (2 : ℝ)^14*L^2 by positivity) (show 0 ≤ (2 : ℝ)^14*L^2 by positivity)
    ha (hb 1 ⟨by norm_num, le_rfl⟩) (fun s hs q _ hq => hb s hs q hq)
  apply he.trans_eq
  rw [cellContourShift_phase]
  have heq : -((99/100 : ℝ)*L⁻¹*dualHessianDistance R.ofLp) =
      -(99/100 : ℝ)*L⁻¹*dualHessianDistance R.ofLp := by ring
  rw [heq]
  ring

#print axioms fullCellSymbol_contour_bound

end Maxwell.Continuum.CellGauge
