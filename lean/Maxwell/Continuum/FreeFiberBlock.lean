import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Literal complex Maxwell block and its inverse

All momentum squares and transposes are bilinear. In particular no complex
conjugation is introduced into the analytic continuation in momentum.
-/

noncomputable section

namespace Maxwell.Continuum.FreeFiber

abbrev Polarization := EuclideanSpace ℂ (Fin 3)
abbrev Momentum := Fin 3 → ℂ
abbrev BlockMatrix := Matrix (Fin 3) (Fin 3) ℂ

def momentumSquare (p : Momentum) : ℂ := ∑ i, p i ^ 2

def momentumOuter (p : Momentum) : BlockMatrix := Matrix.vecMulVec p p

/-- The matrix `p² I - p pᵀ - E I`, with scalar terms collected. -/
def blockMatrix (p : Momentum) (E : ℂ) : BlockMatrix :=
  (momentumSquare p - E) • 1 - momentumOuter p

theorem blockMatrix_eq (p : Momentum) (E : ℂ) :
    blockMatrix p E = momentumSquare p • 1 - momentumOuter p - E • 1 := by
  rw [blockMatrix, sub_smul]
  abel

theorem momentumOuter_square (p : Momentum) :
    momentumOuter p * momentumOuter p = momentumSquare p • momentumOuter p := by
  rw [momentumOuter, Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul]
  congr 1
  simp only [momentumSquare, dotProduct, pow_two]

/-- Explicit inverse formula, with all denominators visible. -/
def inverseMatrix (p : Momentum) (E : ℂ) : BlockMatrix :=
  (momentumSquare p - E)⁻¹ • (1 - E⁻¹ • momentumOuter p)

theorem blockMatrix_mul_numerator (p : Momentum) (E : ℂ) (hE : E ≠ 0) :
    blockMatrix p E * (1 - E⁻¹ • momentumOuter p) = (momentumSquare p - E) • 1 := by
  simp only [blockMatrix, mul_sub, sub_mul, Matrix.smul_mul, Matrix.mul_smul,
    one_mul, mul_one, momentumOuter_square]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem numerator_mul_blockMatrix (p : Momentum) (E : ℂ) (hE : E ≠ 0) :
    (1 - E⁻¹ • momentumOuter p) * blockMatrix p E = (momentumSquare p - E) • 1 := by
  simp only [blockMatrix, mul_sub, sub_mul, Matrix.smul_mul, Matrix.mul_smul,
    one_mul, mul_one, momentumOuter_square]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- One of the two actual matrix inverse identities. -/
theorem blockMatrix_mul_inverseMatrix (p : Momentum) (E : ℂ) (hE : E ≠ 0)
    (hp : momentumSquare p - E ≠ 0) : blockMatrix p E * inverseMatrix p E = 1 := by
  rw [inverseMatrix, Matrix.mul_smul, blockMatrix_mul_numerator p E hE, smul_smul]
  simp only [inv_mul_cancel₀ hp, one_smul]

/-- The other matrix inverse identity; it includes the longitudinal polarization. -/
theorem inverseMatrix_mul_blockMatrix (p : Momentum) (E : ℂ) (hE : E ≠ 0)
    (hp : momentumSquare p - E ≠ 0) : inverseMatrix p E * blockMatrix p E = 1 := by
  rw [inverseMatrix, Matrix.smul_mul, numerator_mul_blockMatrix p E hE, smul_smul]
  simp only [inv_mul_cancel₀ hp, one_smul]

def matrixCLM (M : BlockMatrix) : Polarization →L[ℂ] Polarization :=
  LinearMap.toContinuousLinearMap M.toEuclideanLin

def block (p : Momentum) (E : ℂ) : Polarization →L[ℂ] Polarization :=
  matrixCLM (blockMatrix p E)

def inverseBlock (p : Momentum) (E : ℂ) : Polarization →L[ℂ] Polarization :=
  matrixCLM (inverseMatrix p E)

theorem matrixCLM_mul_apply (M N : BlockMatrix) (v : Polarization) :
    matrixCLM M (matrixCLM N v) = matrixCLM (M * N) v := by
  change M.toEuclideanLin (N.toEuclideanLin v) = (M * N).toEuclideanLin v
  rw [Matrix.toLpLin_mul 2 2 2 M N]
  rfl

@[simp]
theorem matrixCLM_one (v : Polarization) : matrixCLM 1 v = v := by
  change Matrix.toLpLin 2 2 1 v = v
  rw [Matrix.toLpLin_one]
  rfl

theorem block_inverseBlock (p : Momentum) (E : ℂ) (hE : E ≠ 0)
    (hp : momentumSquare p - E ≠ 0) (v : Polarization) :
    block p E (inverseBlock p E v) = v := by
  rw [block, inverseBlock, matrixCLM_mul_apply, blockMatrix_mul_inverseMatrix p E hE hp]
  exact matrixCLM_one v

theorem inverseBlock_block (p : Momentum) (E : ℂ) (hE : E ≠ 0)
    (hp : momentumSquare p - E ≠ 0) (v : Polarization) :
    inverseBlock p E (block p E v) = v := by
  rw [block, inverseBlock, matrixCLM_mul_apply, inverseMatrix_mul_blockMatrix p E hE hp]
  exact matrixCLM_one v

end Maxwell.Continuum.FreeFiber
