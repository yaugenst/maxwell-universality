import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The literal three-dimensional continuum corner blocks

These are the small parity blocks of the continuum Bloch corner. They do not
use the Yee construction and do not assert any estimate for Fourier aliases.
-/

noncomputable section
namespace Maxwell.Continuum.Corner

abbrev Vec := Fin 3 → ℝ
abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ

def normal : Vec := fun _ => 1

/-- Orthogonal projection onto the plane perpendicular to `(1,1,1)`. -/
def projection : Mat := 1 - (1 / 3 : ℝ) • Matrix.vecMulVec normal normal

theorem projection_explicit :
    projection = !![(2 / 3 : ℝ), -(1 / 3), -(1 / 3);
      -(1 / 3), 2 / 3, -(1 / 3); -(1 / 3), -(1 / 3), 2 / 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [projection, normal, Matrix.vecMulVec]

theorem projection_idempotent : projection * projection = projection := by
  rw [projection_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

theorem projection_transpose : projection.transpose = projection := by
  rw [projection_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem projection_mulVec (v : Vec) :
    projection.mulVec v = v - ((∑ i, v i) / 3) • normal := by
  rw [projection_explicit]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, normal] <;> ring

theorem projection_normal : projection.mulVec normal = 0 := by
  rw [projection_mulVec]
  ext i
  norm_num [normal, Fin.sum_univ_succ]

theorem projection_mulVec_transverse (v : Vec) (hv : ∑ i, v i = 0) :
    projection.mulVec v = v := by
  rw [projection_mulVec, hv]
  simp

theorem sum_projection_mulVec (v : Vec) : ∑ i, projection.mulVec v i = 0 := by
  rw [projection_mulVec]
  simp [Fin.sum_univ_succ, normal]
  ring

def coefficientSum (b : Vec) : ℝ := b 0 + b 1 + b 2

def discriminant (b : Vec) : ℝ :=
  (b 0)^2 + (b 1)^2 + (b 2)^2 - b 0 * b 1 - b 0 * b 2 - b 1 * b 2

theorem discriminant_nonneg (b : Vec) : 0 ≤ discriminant b := by
  dsimp [discriminant]
  nlinarith [sq_nonneg (b 0 - b 1), sq_nonneg (b 0 - b 2), sq_nonneg (b 1 - b 2)]

/-- The actual parity-block formula, defined for arbitrary diagonal data. -/
def block (b : Vec) : Mat :=
  projection * Matrix.diagonal b * projection - (coefficientSum b / 2) • projection

theorem block_explicit (b : Vec) :
    block b = !![
      (b 0 - 2 * b 1 - 2 * b 2) / 9, (-b 0 - b 1 + 5 * b 2) / 18,
        (-b 0 + 5 * b 1 - b 2) / 18;
      (-b 0 - b 1 + 5 * b 2) / 18, (-2 * b 0 + b 1 - 2 * b 2) / 9,
        (5 * b 0 - b 1 - b 2) / 18;
      (-b 0 + 5 * b 1 - b 2) / 18, (5 * b 0 - b 1 - b 2) / 18,
        (-2 * b 0 - 2 * b 1 + b 2) / 9] := by
  rw [block]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [projection, normal, Matrix.vecMulVec, Matrix.mul_apply, Matrix.diagonal, Matrix.one_apply,
      Fin.sum_univ_succ, coefficientSum] <;> ring

theorem block_transpose (b : Vec) : (block b).transpose = block b := by
  rw [block_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem block_normal (b : Vec) : (block b).mulVec normal = 0 := by
  rw [block_explicit]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, normal] <;> ring

theorem projection_block (b : Vec) : projection * block b = block b := by
  simp only [block, Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc,
    projection_idempotent]

theorem block_projection (b : Vec) : block b * projection = block b := by
  simp only [block, Matrix.sub_mul, Matrix.smul_mul, Matrix.mul_assoc,
    projection_idempotent]

/-- Direct determinant computation for the literal block. The linear factor
is the normal direction, and the remaining quadratic is the transverse block. -/
theorem block_det_shift (b : Vec) (z : ℝ) :
    Matrix.det (z • (1 : Mat) - block b) =
      z * ((z + coefficientSum b / 6)^2 - discriminant b / 9) := by
  rw [block_explicit, Matrix.det_fin_three]
  norm_num [coefficientSum, discriminant]
  ring

theorem scalar_eq_smul_one (z : ℝ) : Matrix.scalar (Fin 3) z = z • (1 : Mat) := by
  ext i j
  by_cases h : i = j <;> simp [Matrix.scalar_apply, Matrix.diagonal, h]

theorem block_charpoly (b : Vec) :
    (block b).charpoly = Polynomial.X *
      ((Polynomial.X + Polynomial.C (coefficientSum b / 6))^2 -
        Polynomial.C (discriminant b / 9)) := by
  apply Polynomial.funext
  intro z
  rw [Matrix.eval_charpoly, scalar_eq_smul_one, block_det_shift]
  simp

def upperRoot (b : Vec) : ℝ := -coefficientSum b / 6 + Real.sqrt (discriminant b) / 3
def lowerRoot (b : Vec) : ℝ := -coefficientSum b / 6 - Real.sqrt (discriminant b) / 3

theorem block_det_shift_factor (b : Vec) (z : ℝ) :
    Matrix.det (z • (1 : Mat) - block b) = z * (z - upperRoot b) * (z - lowerRoot b) := by
  rw [block_det_shift, ← Real.sq_sqrt (discriminant_nonneg b)]
  dsimp [upperRoot, lowerRoot]
  ring

theorem block_charpoly_upperRoot (b : Vec) :
    (block b).charpoly.IsRoot (upperRoot b) := by
  rw [Polynomial.IsRoot, Matrix.eval_charpoly, scalar_eq_smul_one, block_det_shift_factor]
  simp

theorem block_charpoly_lowerRoot (b : Vec) :
    (block b).charpoly.IsRoot (lowerRoot b) := by
  rw [Polynomial.IsRoot, Matrix.eval_charpoly, scalar_eq_smul_one, block_det_shift_factor]
  simp

theorem block_charpoly_roots (b : Vec) (z : ℝ) :
    (block b).charpoly.IsRoot z ↔ z = 0 ∨ z = upperRoot b ∨ z = lowerRoot b := by
  rw [Polynomial.IsRoot, Matrix.eval_charpoly, scalar_eq_smul_one, block_det_shift_factor]
  simp only [mul_eq_zero, sub_eq_zero, or_assoc]

end Maxwell.Continuum.Corner
