import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Exact matrix identities for the local spectral polynomial

These identities apply to the full complex Hermitian electric fiber. In
particular the squared residual is not projected off the center cluster.
The quantitative Taylor and inertia premises are separate inputs to the
neighborhood argument; no neighborhood-minimum conclusion is assumed here.
-/

namespace Maxwell.Spectral

open Matrix
open scoped Matrix ComplexConjugate

variable {n m : Type*} [Fintype n] [DecidableEq n]

def shiftedMatrix (A : Matrix n n ℂ) (E : ℝ) : Matrix n n ℂ :=
  A - (E : ℂ) • 1

def edgePolynomial (A : Matrix n n ℂ) (E b : ℝ) : Matrix n n ℂ :=
  ((b - E : ℝ) : ℂ) • shiftedMatrix A E - shiftedMatrix A E * shiftedMatrix A E

omit [Fintype n] in
theorem shiftedMatrix_hermitian (A : Matrix n n ℂ) (E : ℝ)
    (hA : A.IsHermitian) : (shiftedMatrix A E).IsHermitian := by
  apply hA.sub
  exact isHermitian_one.smul (by change star (E : ℂ) = (E : ℂ); simp)

theorem edgePolynomial_eq_product (A : Matrix n n ℂ) (E b : ℝ) :
    edgePolynomial A E b = (A - (E : ℂ) • 1) * ((b : ℂ) • 1 - A) := by
  have hb : (b : ℂ) • (1 : Matrix n n ℂ) - A =
      ((b - E : ℝ) : ℂ) • 1 - shiftedMatrix A E := by
    simp only [shiftedMatrix, Complex.ofReal_sub, sub_smul]
    abel
  rw [hb, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
  rfl

theorem edgePolynomial_hermitian (A : Matrix n n ℂ) (E b : ℝ)
    (hA : A.IsHermitian) : (edgePolynomial A E b).IsHermitian := by
  have hX := shiftedMatrix_hermitian A E hA
  apply (hX.smul (by change star (((b - E : ℝ) : ℂ)) = _; simp)).sub
  change (shiftedMatrix A E * shiftedMatrix A E).conjTranspose = _
  rw [Matrix.conjTranspose_mul, hX.eq]

/-- The polynomial's negative term is the Gram matrix of the complete
residual `(A-E)F`. This is the source of the full residual Gram obligation. -/
theorem compressed_polynomial_identity (A : Matrix n n ℂ) (E b : ℝ)
    (F : Matrix n m ℂ) (hA : A.IsHermitian) :
    F.conjTranspose * edgePolynomial A E b * F =
      ((b - E : ℝ) : ℂ) • (F.conjTranspose * shiftedMatrix A E * F) -
        (shiftedMatrix A E * F).conjTranspose * (shiftedMatrix A E * F) := by
  have hX := shiftedMatrix_hermitian A E hA
  simp only [edgePolynomial, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.conjTranspose_mul, hX.eq]
  simp only [Matrix.mul_assoc]

omit [DecidableEq n] in
/-- Opposite inversion sectors remove the mixed terms of a residual square.
This statement permits rectangular even/odd residual blocks. -/
theorem orthogonal_residual_square (R_even R_odd : Matrix n m ℂ)
    (horth : R_even.conjTranspose * R_odd = 0) :
    (R_even + R_odd).conjTranspose * (R_even + R_odd) =
      R_even.conjTranspose * R_even + R_odd.conjTranspose * R_odd := by
  have horth' : R_odd.conjTranspose * R_even = 0 := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] using congrArg Matrix.conjTranspose horth
  simp only [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, horth,
    horth', add_zero, zero_add]

omit [DecidableEq n] in
/-- The trial matrix has exactly its identity Gram plus the derivative Gram;
it is not treated as an orthonormal matrix away from the center. -/
theorem trial_gram_identity [DecidableEq m] (Phi Y : Matrix n m ℂ)
    (hPhi : Phi.conjTranspose * Phi = 1)
    (horth : Phi.conjTranspose * Y = 0) :
    (Phi - Y).conjTranspose * (Phi - Y) = 1 + Y.conjTranspose * Y := by
  have horth' : Y.conjTranspose * Phi = 0 := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] using congrArg Matrix.conjTranspose horth
  simp only [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub,
    hPhi, horth, horth', sub_zero, zero_sub, sub_neg_eq_add]

end Maxwell.Spectral
