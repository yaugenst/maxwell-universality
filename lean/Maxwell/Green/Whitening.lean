import Maxwell.Green.Placement
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-! The metric used for integer placement is constructed from the actual
positive definite Hessian by continuous functional calculus. -/

noncomputable section

namespace Maxwell.Green

open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator

theorem matrixAction_inner_symm (A : Mat3) (hA : A.IsHermitian) (x y : Vec3) :
    inner ℝ (matrixAction A x) y = inner ℝ x (matrixAction A y) := by
  have hstar : star (matrixAction A) = matrixAction A := by
    change star (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) A) =
      Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) A
    rw [← map_star]
    exact congrArg _ hA.eq
  change (matrixAction A).adjoint = matrixAction A at hstar
  simpa only [hstar] using
    (ContinuousLinearMap.adjoint_inner_left (matrixAction A) y x)

/-- A positive Hessian supplies an actual square root and its inverse.  The
Euclidean norm in these coordinates is exactly the Hessian quadratic form. -/
theorem exists_hessian_whitening (A : Mat3) (hA : A.PosDef) :
    ∃ Q P : Mat3, Q * Q = A ∧ P * Q = 1 ∧ Q * P = 1 ∧
      Q.IsHermitian ∧ P.IsHermitian ∧
      (∀ x y : Vec3, inner ℝ (matrixAction P x) y =
        inner ℝ x (matrixAction P y)) ∧
      ∀ x : Vec3, ‖matrixAction Q x‖ ^ 2 = inner ℝ x (matrixAction A x) := by
  let Q : Mat3 := CFC.sqrt A
  have hQsq : Q * Q = A := by
    simpa only [Q, pow_two] using CFC.sq_sqrt A hA.posSemidef.nonneg
  have hQunit : IsUnit Q := by
    apply (isUnit_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp
    simpa only [pow_two, hQsq] using hA.isUnit
  have hQ : Q.IsHermitian := (CFC.sqrt_nonneg A).posSemidef.isHermitian
  refine ⟨Q, Q⁻¹, hQsq,
    Matrix.nonsing_inv_mul Q (Matrix.isUnit_iff_isUnit_det Q |>.mp hQunit),
    Matrix.mul_nonsing_inv Q (Matrix.isUnit_iff_isUnit_det Q |>.mp hQunit),
    hQ, hQ.inv, matrixAction_inner_symm Q⁻¹ hQ.inv, ?_⟩
  intro x
  calc
    ‖matrixAction Q x‖ ^ 2 = inner ℝ (matrixAction Q x) (matrixAction Q x) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = inner ℝ x (matrixAction Q (matrixAction Q x)) :=
      matrixAction_inner_symm Q hQ x (matrixAction Q x)
    _ = inner ℝ x (matrixAction A x) := by
      have hmul : matrixAction A = matrixAction Q * matrixAction Q := by
        rw [← map_mul, hQsq]
      rw [hmul]
      rfl

/-- Riesz representation turns the actual symmetric bilinear Hessian into
a positive definite matrix in the fixed physical coordinates. -/
theorem exists_positive_hessian_matrix
    (B : Vec3 →L[ℝ] Vec3 →L[ℝ] ℝ)
    (hB : ∀ x y, B x y = B y x)
    (hpos : ∀ x : Vec3, x ≠ 0 → 0 < B x x) :
    ∃ A : Mat3, A.PosDef ∧ ∀ x y : Vec3,
      inner ℝ (matrixAction A x) y = B x y := by
  let T : Vec3 →L[ℝ] Vec3 :=
    (InnerProductSpace.toDual ℝ Vec3).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp B
  have hTinner (x y : Vec3) : inner ℝ (T x) y = B x y := by
    change inner ℝ ((InnerProductSpace.toDual ℝ Vec3).symm (B x)) y = _
    exact InnerProductSpace.toDual_symm_apply
  have hTsym : T.toLinearMap.IsSymmetric := by
    intro x y
    change inner ℝ (T x) y = inner ℝ x (T y)
    rw [hTinner, real_inner_comm, hTinner, hB]
  let A : Mat3 := (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)).symm T
  have hTA : matrixAction A = T := by simp [A, matrixAction]
  have hA : A.IsHermitian := by
    apply Matrix.isHermitian_iff_isSelfAdjoint.mpr
    exact hTsym.isSelfAdjoint.map (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)).symm
  refine ⟨A, Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨hA, ?_⟩, ?_⟩
  · intro x hx
    have hx' : WithLp.toLp 2 x ≠ (0 : Vec3) := by simpa using hx
    have hp := hpos (WithLp.toLp 2 x) hx'
    rw [← hTinner, ← hTA, real_inner_comm, Matrix.inner_toEuclideanCLM] at hp
    simpa using hp
  · intro x y
    rw [hTA, hTinner]

/-- The square-root metric is obtained directly from a positive symmetric
bilinear Hessian, with no supplied factorization or inverse. -/
theorem exists_bilinear_hessian_whitening
    (B : Vec3 →L[ℝ] Vec3 →L[ℝ] ℝ)
    (hB : ∀ x y, B x y = B y x)
    (hpos : ∀ x : Vec3, x ≠ 0 → 0 < B x x) :
    ∃ Q P : Mat3, P * Q = 1 ∧ Q * P = 1 ∧ P.IsHermitian ∧
      (∀ x y : Vec3, inner ℝ (matrixAction P x) y =
        inner ℝ x (matrixAction P y)) ∧
      ∀ x : Vec3, ‖matrixAction Q x‖ ^ 2 = B x x := by
  obtain ⟨A, hA, hAB⟩ := exists_positive_hessian_matrix B hB hpos
  obtain ⟨Q, P, _, hPQ, hQP, _, hP, hPsym, hmetric⟩ := exists_hessian_whitening A hA
  refine ⟨Q, P, hPQ, hQP, hP, hPsym, fun x => ?_⟩
  rw [hmetric, real_inner_comm, hAB]

end Maxwell.Green
