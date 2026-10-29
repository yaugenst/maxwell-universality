import Maxwell.Continuum.PeriodicBandBilinear
import Maxwell.Continuum.PeriodicBandEllipticity

/-! The actual Hessian is a real diagonal matrix. Coordinate reflection
kills its mixed terms, and the complete quadratic form is identified. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber

theorem bandQuadratic_diagonal (t : Momentum) :
    bandQuadratic t = ∑ j : Fin 3, bandQuadratic (basisVector j) * (t j)^2 := by
  rw [bandBilinear_expansion]
  simp only [Fin.sum_univ_three, bandQuadratic_eq_bilinear]
  have h01 := bandBilinear_cross_cancel 0 1 (by decide)
  have h02 := bandBilinear_cross_cancel 0 2 (by decide)
  have h12 := bandBilinear_cross_cancel 1 2 (by decide)
  linear_combination (t 0 * t 1) * h01 + (t 0 * t 2) * h02 + (t 1 * t 2) * h12

theorem basisVector_real (j : Fin 3) : basisVector j = realMomentum (Pi.single j 1) := by
  funext k
  simp only [basisVector_apply, realMomentum, Pi.single_apply]
  split_ifs <;> simp

theorem bandQuadratic_basis_im_zero (j : Fin 3) : (bandQuadratic (basisVector j)).im = 0 := by
  rw [basisVector_real]
  exact bandQuadratic_im_zero _

def scaledHessian : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal (fun j => (bandQuadratic (basisVector j)).re)

def hessian : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal (fun j => (bandQuadratic (basisVector j)).re / backgroundAmplitude)

theorem scaledHessian_form (t : Corner.Vec) :
    dotProduct t (scaledHessian.mulVec t) = (bandQuadratic (realMomentum t)).re := by
  rw [bandQuadratic_diagonal]
  simp only [scaledHessian, Matrix.mulVec, Matrix.diagonal_apply, dotProduct,
    Complex.re_sum, realMomentum]
  apply Finset.sum_congr rfl
  intro j _
  simp [Complex.mul_re, ← Complex.ofReal_pow, bandQuadratic_basis_im_zero]
  ring

theorem hessian_form (t : Corner.Vec) :
    dotProduct t (hessian.mulVec t) = (bandQuadratic (realMomentum t)).re / backgroundAmplitude := by
  rw [← scaledHessian_form]
  simp only [hessian, scaledHessian, Matrix.mulVec, Matrix.diagonal_apply, dotProduct,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  simp
  ring

theorem hessian_bounds (t : Corner.Vec) :
    (2 * backgroundAmplitude)⁻¹ * dotProduct t t ≤ dotProduct t (hessian.mulVec t) ∧
      dotProduct t (hessian.mulVec t) ≤ (256 / backgroundAmplitude) * dotProduct t t := by
  rw [hessian_form]
  have h := bandQuadratic_bounds t
  constructor
  · apply (le_div_iff₀ backgroundAmplitude_pos).mpr
    have heq : ((2 * backgroundAmplitude)⁻¹ * dotProduct t t) * backgroundAmplitude =
        (1 / 2 : ℝ) * dotProduct t t := by
      field_simp [backgroundAmplitude_pos.ne']
    rw [heq]
    exact h.1
  · apply (div_le_iff₀ backgroundAmplitude_pos).mpr
    have heq : (256 / backgroundAmplitude * dotProduct t t) * backgroundAmplitude =
        256 * dotProduct t t := by
      field_simp [backgroundAmplitude_pos.ne']
    rw [heq]
    exact h.2

end Maxwell.Continuum.PeriodicBand
