import Maxwell.Continuum.PeriodicBandHessian
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! The Hessian error in the Euclidean operator norm, with the actual
diagonal quadratic coefficient identified in the continuum band. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber CornerBridge
open scoped Matrix.Norms.L2Operator

def cornerHessian : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal (fun j => Real.pi ^ 2 * Corner.hessianCoefficient j)

theorem bandQuadratic_basis_comparison (j : Fin 3) :
    |(bandQuadratic (basisVector j)).re - Real.pi ^ 2 * Corner.hessianCoefficient j| ≤
      (2 : ℝ)^34 * backgroundAmplitude := by
  have h := bandQuadratic_real_comparison (Pi.single j 1)
  rw [← basisVector_real] at h
  simpa [cornerQuadratic, dotProduct, Pi.single_apply] using h

theorem scaled_hessian_eq : backgroundAmplitude • hessian = scaledHessian := by
  ext j k
  by_cases hjk : j = k
  · subst k
    simp only [hessian, scaledHessian, Matrix.smul_apply, Matrix.diagonal_apply_eq,
      smul_eq_mul]
    field_simp [backgroundAmplitude_pos.ne']
  · simp [hessian, scaledHessian, Matrix.diagonal_apply_ne _ hjk]

theorem scaled_hessian_error_eq : backgroundAmplitude • hessian - cornerHessian =
    Matrix.diagonal (fun j =>
      (bandQuadratic (basisVector j)).re - Real.pi ^ 2 * Corner.hessianCoefficient j) := by
  rw [scaled_hessian_eq]
  ext j k
  by_cases hjk : j = k
  · subst k
    simp [scaledHessian, cornerHessian]
  · simp [scaledHessian, cornerHessian, Matrix.diagonal_apply_ne _ hjk]

/-- This is the operator norm on Euclidean three-space, not an entrywise norm. -/
theorem hessian_operator_error :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3)
      (backgroundAmplitude • hessian - cornerHessian)‖ ≤
      (2 : ℝ)^40 * backgroundAmplitude := by
  have hρ := backgroundAmplitude_pos
  rw [Matrix.l2_opNorm_toEuclideanCLM, scaled_hessian_error_eq, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  rw [Real.norm_eq_abs]
  exact (bandQuadratic_basis_comparison j).trans
    (mul_le_mul_of_nonneg_right (by norm_num) backgroundAmplitude_pos.le)

theorem hessian_diagonal_error (j : Fin 3) :
    |backgroundAmplitude * hessian j j - Real.pi ^ 2 * Corner.hessianCoefficient j| ≤
      ((2 : ℝ)^60)⁻¹ := by
  have h := bandQuadratic_basis_comparison j
  have heq : backgroundAmplitude * hessian j j = (bandQuadratic (basisVector j)).re := by
    simp only [hessian, Matrix.diagonal_apply_eq]
    field_simp [backgroundAmplitude_pos.ne']
  rw [heq]
  exact h.trans (by norm_num [backgroundAmplitude])

def hessianOperator : Space →L[ℝ] Space :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin 3) hessian

theorem hessianOperator_inner (v : Space) :
    inner ℝ v (hessianOperator v) = dotProduct v.ofLp (hessian.mulVec v.ofLp) :=
  Matrix.inner_toEuclideanCLM hessian v v

theorem hessianOperator_bounds (v : Space) :
    (2 * backgroundAmplitude)⁻¹ * ‖v‖^2 ≤ inner ℝ v (hessianOperator v) ∧
      inner ℝ v (hessianOperator v) ≤ (256 / backgroundAmplitude) * ‖v‖^2 := by
  rw [hessianOperator_inner]
  have heq : ‖v‖^2 = dotProduct v.ofLp v.ofLp := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [dotProduct, Real.norm_eq_abs, pow_two]
  rw [heq]
  exact hessian_bounds v.ofLp

theorem hessianOperator_nonneg (v : Space) : 0 ≤ inner ℝ v (hessianOperator v) :=
  (mul_nonneg (inv_nonneg.mpr (mul_nonneg (by norm_num) backgroundAmplitude_pos.le))
    (sq_nonneg ‖v‖)).trans (hessianOperator_bounds v).1

end Maxwell.Continuum.PeriodicBand
