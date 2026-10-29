import Maxwell.Continuum.PeriodicImaginaryBand

/-! The actual band Hessian on complex momentum, with separate real and
imaginary quadratic energies and the quantitative Euclidean lower bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber

def hessianEnergy (q : Corner.Vec) : ℝ := dotProduct q (hessian.mulVec q)

def shiftedMomentum (q b : Corner.Vec) : Momentum :=
  realMomentum q + Complex.I • realMomentum b

theorem hessianEnergy_diagonal (q : Corner.Vec) :
    hessianEnergy q = ∑ j : Fin 3, hessian j j * (q j)^2 := by
  simp only [hessianEnergy, dotProduct, hessian, Matrix.mulVec_diagonal,
    Matrix.diagonal_apply_eq]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem physicalQuadratic_diagonal (q : Momentum) :
    physicalQuadratic q = ∑ j : Fin 3, (hessian j j : ℂ) * (q j)^2 := by
  rw [physicalQuadratic, bandQuadratic_diagonal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hj := physicalQuadratic_basis j
  unfold physicalQuadratic at hj
  rw [← hj]
  ring

theorem shifted_quadratic_re (q b : Corner.Vec) :
    (physicalQuadratic (shiftedMomentum q b)).re = hessianEnergy q - hessianEnergy b := by
  rw [physicalQuadratic_diagonal, Complex.re_sum, hessianEnergy_diagonal,
    hessianEnergy_diagonal, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp [shiftedMomentum, realMomentum, Complex.mul_re, Complex.mul_im, pow_two]
  ring

theorem hessianEnergy_lower (q : Corner.Vec) :
    (2 * backgroundAmplitude)⁻¹ * ‖realMomentum q‖^2 ≤ hessianEnergy q :=
  (mul_le_mul_of_nonneg_left (norm_realMomentum_sq_le_dot q)
    (inv_nonneg.mpr (mul_nonneg (by norm_num) backgroundAmplitude_pos.le))).trans
      (hessian_bounds q).1

theorem hessianEnergy_nonneg (q : Corner.Vec) : 0 ≤ hessianEnergy q :=
  (mul_nonneg (inv_nonneg.mpr (mul_nonneg (by norm_num) backgroundAmplitude_pos.le))
    (sq_nonneg _)).trans (hessianEnergy_lower q)

theorem norm_sq_le_hessianEnergy (q : Corner.Vec) : ‖realMomentum q‖^2 ≤ hessianEnergy q := by
  have hc : (1 : ℝ) ≤ (2 * backgroundAmplitude)⁻¹ := by norm_num [backgroundAmplitude]
  have hl : ‖realMomentum q‖^2 ≤ (2 * backgroundAmplitude)⁻¹ * ‖realMomentum q‖^2 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (sq_nonneg ‖realMomentum q‖)
  exact hl.trans (hessianEnergy_lower q)

theorem shiftedMomentum_norm_le (q b : Corner.Vec) :
    ‖shiftedMomentum q b‖ ≤ ‖realMomentum q‖ + ‖realMomentum b‖ := by
  simpa only [shiftedMomentum, norm_smul, Complex.norm_I, one_mul] using
    norm_add_le (realMomentum q) (Complex.I • realMomentum b)

theorem shiftedMomentum_norm_fourth (q b : Corner.Vec) :
    ‖shiftedMomentum q b‖^4 ≤ 8 * (‖realMomentum q‖^4 + ‖realMomentum b‖^4) := by
  have hp := add_pow_le (norm_nonneg (realMomentum q)) (norm_nonneg (realMomentum b)) 4
  norm_num at hp
  exact (pow_le_pow_left₀ (norm_nonneg _) (shiftedMomentum_norm_le q b) 4).trans hp

end Maxwell.Continuum.PeriodicBand
