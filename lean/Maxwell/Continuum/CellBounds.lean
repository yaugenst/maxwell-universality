import Maxwell.Continuum.DerivativeCellContour
import Maxwell.Continuum.DerivativeCellLocalization
import Maxwell.Continuum.FullCellBounds
import Maxwell.Continuum.CellDistance
import Maxwell.Continuum.AuxiliaryResolventDerivative

/-! The actual off-support and periodization estimates, including both
operators in the paper and the weak spatial derivative identity. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellGauge

open Auxiliary Bloch PeriodicBand MasterConstants

theorem cell_metric_exponential_le {L : ℝ} (hL : 0 < L) (a b : Bloch.Alias) :
    Real.exp (-(99/100 : ℝ)*L⁻¹*dualHessianDistance (latticeShift a-latticeShift b).ofLp) ≤
      Real.exp (-cs * paperCellDistance a b / L) := by
  apply Real.exp_le_exp.mpr
  have hd := mul_le_mul_of_nonneg_left (paperCellDistance_metric_rate a b) (inv_nonneg.mpr hL.le)
  calc
    _ = -(L⁻¹ * ((99/100 : ℝ) * dualHessianDistance (latticeShift a-latticeShift b).ofLp)) := by ring
    _ ≤ -(L⁻¹ * (cs * paperCellDistance a b)) := neg_le_neg hd
    _ = _ := by ring

theorem resolventSpatialBlock_paper_exponential {L z σ : ℝ} (hL : Ls ≤ L)
    (D : Calibration L⁻¹ z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4/64) (a b : Bloch.Alias) :
    ‖resolventSpatialBlock D hσ0 hσ a b‖ ≤ Cs * L^4 *
      (Real.exp (-cs * paperCellDistance a b / L) + Real.exp (-cs*L)) := by
  have hb := resolventSpatialBlock_exponential hL D hσ0 hσ a b
  have hc : (2 : ℝ)^69 ≤ Cs := fixed_power_le_Cs (by have := exponent_large; omega)
  have hL1 := length_ge_one hL
  have h2 : L^2 ≤ L^4 := by nlinarith [sq_nonneg (L^2-1)]
  apply hb.trans
  exact mul_le_mul (mul_le_mul hc h2 (sq_nonneg L) Cs_pos.le)
    (add_le_add (cell_metric_exponential_le (length_pos hL) a b) le_rfl)
    (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    (mul_nonneg Cs_pos.le (pow_nonneg (length_pos hL).le 4))

theorem derivativeResolventSpatialBlock_paper_exponential {L z σ : ℝ} (hL : Ls ≤ L)
    (D : Calibration L⁻¹ z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4/64)
    (j : Fin 3) (a b : Bloch.Alias) :
    ‖derivativeResolventSpatialBlock D hσ0 hσ j a b‖ ≤ Cs * L^4 *
      (Real.exp (-cs * paperCellDistance a b / L) + Real.exp (-cs*L)) := by
  have hb := derivativeResolventSpatialBlock_exponential hL D hσ0 hσ j a b
  have hc : (2 : ℝ)^87 ≤ Cs := fixed_power_le_Cs (by have := exponent_large; omega)
  apply hb.trans
  exact mul_le_mul (mul_le_mul_of_nonneg_right hc (by positivity))
    (add_le_add (cell_metric_exponential_le (length_pos hL) a b) le_rfl)
    (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    (mul_nonneg Cs_pos.le (pow_nonneg (length_pos hL).le 4))

#print axioms resolventSpatialBlock_paper_exponential
#print axioms derivativeResolventSpatialBlock_paper_exponential
#print axioms derivativeResolventSpatialBlock_gevrey
#print axioms derivativeResolventSpatialBlock_sum_exists
#print axioms Auxiliary.resolvent_weak_derivative

end Maxwell.Continuum.CellGauge
