import Maxwell.Continuum.PeriodicImaginaryPole
import Mathlib.Analysis.Complex.ExponentialBounds

/-! The action of the constructed imaginary pole in the literal integer
placement direction, including the strict logarithmic margin. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open Auxiliary

attribute [local irreducible] imaginaryPole hessian

theorem placementDiagonal_pos (j : Fin 3) : 0 < (placementDiagonal j : ℝ) := by
  fin_cases j <;> norm_num [placementDiagonal]

theorem placement_sqrt_ratio_upper (j : Fin 3) :
    (placementDiagonal j : ℝ) / Real.sqrt (hessian j j) ≤ 101 / 100 := by
  apply (div_le_iff₀ (Real.sqrt_pos.mpr (hessian_diagonal_positive j))).mpr
  have hb := (placement_diagonal_squared j).2
  have hs := Real.sq_sqrt (hessian_diagonal_positive j).le
  have hn := Real.sqrt_nonneg (hessian j j)
  nlinarith

def poleAction {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) : ℝ :=
  2 * h⁻¹ * (placementDiagonal j : ℝ) * imaginaryPole D hh j

theorem poleAction_pos {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) : 0 < poleAction D hh j :=
  mul_pos (mul_pos (mul_pos (by norm_num) (inv_pos.mpr D.h_pos)) (placementDiagonal_pos j))
    (imaginaryPole_pos D hh j)

theorem poleAction_bound {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    poleAction D hh j ≤ 2 * (101 / 100 : ℝ)^2 := by
  have hcoef : 0 ≤ 2 * h⁻¹ * (placementDiagonal j : ℝ) :=
    mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr D.h_pos.le)) (placementDiagonal_pos j).le
  calc
    _ ≤ 2 * h⁻¹ * (placementDiagonal j : ℝ) *
        ((101 / 100 : ℝ) * h / Real.sqrt (hessian j j)) :=
      mul_le_mul_of_nonneg_left (imaginaryPole_bounds D hh j).2 hcoef
    _ = (2 * (101 / 100 : ℝ)) *
        ((placementDiagonal j : ℝ) / Real.sqrt (hessian j j)) := by
      field_simp [D.h_pos.ne']
    _ ≤ (2 * (101 / 100 : ℝ)) * (101 / 100) :=
      mul_le_mul_of_nonneg_left (placement_sqrt_ratio_upper j) (by norm_num)
    _ = _ := by ring

theorem action_logarithmic_margin :
    2 * (101 / 100 : ℝ)^2 < Real.log 8 - 1 / 50 := by
  rw [show (8 : ℝ) = 2^3 by norm_num, Real.log_pow]
  have h := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith

theorem poleAction_log_margin {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    poleAction D hh j < Real.log 8 - 1 / 50 :=
  (poleAction_bound D hh j).trans_lt action_logarithmic_margin

end Maxwell.Continuum.PeriodicBand
