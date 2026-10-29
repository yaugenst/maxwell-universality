import Maxwell.Continuum.CornerEigenvector
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Exact corner resolvent quadratic forms

The three matrices here are the parity blocks reached by flipping one sign
of the selected parity. Their literal inverses exist, and the displayed
quadratic forms give the three claimed coefficients of `H₀ / π²`.
Identification with a continuum Bloch Hessian still needs the analytic
perturbation argument and its alias-remainder estimates.
-/

noncomputable section
namespace Maxwell.Continuum.Corner

def flippedParity (j : Fin 3) : Parity :=
  ![(false, false, false), (true, true, false), (true, false, true)] j

theorem flippedParity_ne_selected (j : Fin 3) : flippedParity j ≠ selectedParity := by
  fin_cases j <;> decide

def shiftedFlippedBlock (j : Fin 3) : Mat := lambdaStar • 1 - parityBlock (flippedParity j)

theorem shiftedFlippedBlock_det_ne_zero (j : Fin 3) : (shiftedFlippedBlock j).det ≠ 0 := by
  have hu := other_root_gap (flippedParity j) true (by
    simpa using flippedParity_ne_selected j)
  have hl := other_root_gap (flippedParity j) false (by simp)
  rw [shiftedFlippedBlock, parityBlock, block_det_shift_factor]
  apply mul_ne_zero (mul_ne_zero lambdaStar_pos.ne' _) _
  · change lambdaStar - parityRoot (flippedParity j) true ≠ 0
    linarith
  · change lambdaStar - parityRoot (flippedParity j) false ≠ 0
    linarith

/-- Explicit solutions of the three shifted systems, in `ℚ(√19)`. -/
def resolventVector (j : Fin 3) : Vec := ![
  ![(676 + 197 * Real.sqrt 19) / 465, (-549 - 63 * Real.sqrt 19) / 310,
      (59 - 41 * Real.sqrt 19) / 186],
  ![(8 + Real.sqrt 19) / 5, -(7 / 6) - Real.sqrt 19 / 3,
      -(13 / 30) + 2 * Real.sqrt 19 / 15],
  ![-(1 / 8) + Real.sqrt 19 / 8, 13 / 120 - Real.sqrt 19 / 30,
      1 / 60 - 11 * Real.sqrt 19 / 120]] j

/-- The explicit vectors solve the actual matrix systems. -/
theorem resolventVector_solves (j : Fin 3) :
    (shiftedFlippedBlock j).mulVec (resolventVector j) = topVector := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 19)
  rw [shiftedFlippedBlock, parityBlock, block_explicit]
  ext i
  fin_cases j <;> fin_cases i <;>
    norm_num [flippedParity, parityCoefficients, sign, resolventVector, topVector, lambdaStar,
      Matrix.mulVec, Matrix.one_apply, dotProduct, Fin.sum_univ_succ] <;> nlinarith

/-- Identification with the genuine nonsingular inverse, rather than a
matrix supplied with an assumed inverse property. -/
theorem resolventVector_eq_inverse (j : Fin 3) :
    resolventVector j = (shiftedFlippedBlock j)⁻¹.mulVec topVector := by
  rw [← resolventVector_solves j, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (shiftedFlippedBlock_det_ne_zero j)),
    Matrix.one_mulVec]

def hessianCoefficient (j : Fin 3) : ℝ :=
  ![47 / 31 + 352 * Real.sqrt 19 / 589,
    2 + 11 * Real.sqrt 19 / 38,
    1 / 8 + 11 * Real.sqrt 19 / 152] j

/-- Exact arithmetic establishes each resolvent Rayleigh quotient. -/
theorem resolvent_rayleigh (j : Fin 3) :
    dotProduct topVector ((shiftedFlippedBlock j)⁻¹.mulVec topVector) /
      dotProduct topVector topVector = hessianCoefficient j := by
  rw [← resolventVector_eq_inverse]
  apply (div_eq_iff topVector_normSq_pos.ne').mpr
  rw [topVector_normSq]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 19)
  fin_cases j <;> norm_num [topVector, resolventVector, hessianCoefficient,
    dotProduct, Fin.sum_univ_succ] <;> nlinarith

theorem normalized_resolvent_rayleigh (j : Fin 3) :
    dotProduct normalizedTopVector ((shiftedFlippedBlock j)⁻¹.mulVec normalizedTopVector) =
      hessianCoefficient j := by
  rw [normalizedTopVector, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  calc
    _ = dotProduct topVector ((shiftedFlippedBlock j)⁻¹.mulVec topVector) /
        ((Real.sqrt (dotProduct topVector topVector)) ^ 2) := by ring
    _ = hessianCoefficient j := by
      rw [Real.sq_sqrt topVector_normSq_pos.le]
      exact resolvent_rayleigh j

theorem hessianCoefficient_bounds (j : Fin 3) :
    1 / 14 ≤ hessianCoefficient j ∧ hessianCoefficient j ≤ 20 := by
  have hl := sqrt_nineteen_bounds.1
  have hu := sqrt_nineteen_bounds.2
  fin_cases j <;> norm_num [hessianCoefficient] <;> constructor <;> linarith

end Maxwell.Continuum.Corner
