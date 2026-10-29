import Maxwell.Continuum.PeriodicPoleAction

/-! The pole in scaled momentum coordinates, with the unit-ball bound
used by the literal analytic source numerator. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary

attribute [local irreducible] imaginaryPole hessian

theorem sqrt_hessian_diagonal_ge_two (j : Fin 3) : 2 ≤ Real.sqrt (hessian j j) := by
  have hH : 4 ≤ hessian j j :=
    (by norm_num [backgroundAmplitude] : (4 : ℝ) ≤ (2 * backgroundAmplitude)⁻¹).trans
      (hessian_diagonal_bounds j).1
  have hs := Real.sqrt_le_sqrt hH
  rw [show (4 : ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] at hs
  exact hs

theorem imaginaryPole_scaled_bounds {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    (99 / 100 : ℝ) / Real.sqrt (hessian j j) ≤ imaginaryPole D hh j / h ∧
      imaginaryPole D hh j / h ≤ (101 / 100 : ℝ) / Real.sqrt (hessian j j) := by
  have hlo := div_le_div_of_nonneg_right (imaginaryPole_bounds D hh j).1 D.h_pos.le
  have hhi := div_le_div_of_nonneg_right (imaginaryPole_bounds D hh j).2 D.h_pos.le
  have hl : ((99 / 100 : ℝ) * h / Real.sqrt (hessian j j)) / h =
      (99 / 100 : ℝ) / Real.sqrt (hessian j j) := by field_simp [D.h_pos.ne']
  have hr : ((101 / 100 : ℝ) * h / Real.sqrt (hessian j j)) / h =
      (101 / 100 : ℝ) / Real.sqrt (hessian j j) := by field_simp [D.h_pos.ne']
  exact ⟨hl ▸ hlo, hr ▸ hhi⟩

theorem imaginaryPole_scaled_le_one {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) : imaginaryPole D hh j / h ≤ 1 := by
  apply (imaginaryPole_scaled_bounds D hh j).2.trans
  apply (div_le_one (Real.sqrt_pos.mpr (hessian_diagonal_positive j))).mpr
  exact (by norm_num : (101 / 100 : ℝ) ≤ 2).trans (sqrt_hessian_diagonal_ge_two j)

theorem imaginaryPole_le_inverse_scale {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) : imaginaryPole D hh j ≤ h :=
  (div_le_one D.h_pos).mp (imaginaryPole_scaled_le_one D hh j)

theorem imaginaryPole_lt_two_inverse_scale {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) : imaginaryPole D hh j < 2 * h :=
  (imaginaryPole_le_inverse_scale D hh j).trans_lt (by linarith [D.h_pos])

end Maxwell.Continuum.PeriodicBand
