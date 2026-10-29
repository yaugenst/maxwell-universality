import Maxwell.Continuum.FullCellKernel
import Maxwell.Continuum.PeriodicCellContour

/-! Exponential localization of the complete physical cutoff resolvent.
The projections are literal spatial indicators and the decay rate is
the actual Hessian metric, with the strict 0.99 tube margin. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellGauge

open Auxiliary Bloch OperatorFourier PeriodicBand MasterConstants

theorem resolventSpatialBlock_exponential {L z σ : ℝ} (hL : Ls ≤ L)
    (D : Calibration L⁻¹ z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4 / 64)
    (a b : Bloch.Alias) :
    ‖resolventSpatialBlock D hσ0 hσ a b‖ ≤ (2 : ℝ)^69 * L^2 *
      (Real.exp (-(99/100 : ℝ) * L⁻¹ *
        dualHessianDistance (latticeShift a - latticeShift b).ofLp) + Real.exp (-cs*L)) := by
  have hc := fullCellSymbol_contour_bound hL D hσ0 hσ (latticeShift a - latticeShift b)
  have he : (fun q : Space => (Well.chi smallRadius q : ℂ) •
      fullCellSymbol z σ (realMomentumMap q)) = cutoffFullCellSymbol z σ := rfl
  rw [he, neg_sub] at hc
  apply (resolventSpatialBlock_norm_le_kernel D hσ0 hσ a b).trans
  apply (mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 64)).trans_eq
  have hnum : (64 : ℝ) * 2^63 = 2^69 := by norm_num
  rw [show (64 : ℝ) * (2^63 * L^2 *
      (Real.exp (-(99/100 : ℝ) * L⁻¹ *
        dualHessianDistance (latticeShift a - latticeShift b).ofLp) + Real.exp (-cs*L))) =
      (64 * 2^63) * L^2 *
      (Real.exp (-(99/100 : ℝ) * L⁻¹ *
        dualHessianDistance (latticeShift a - latticeShift b).ofLp) + Real.exp (-cs*L)) by ring,
    hnum]

#print axioms resolventSpatialBlock_exponential

end Maxwell.Continuum.CellGauge
