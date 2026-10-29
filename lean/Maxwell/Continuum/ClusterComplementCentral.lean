import Maxwell.Continuum.FreeFiberNoncentral
import Mathlib.Analysis.CStarAlgebra.Basic

/-!
# Fixed central longitudinal compression

The projection uses the real corner direction and is fixed as the complex
momentum changes. The longitudinal scalar includes the exact quadratic
correction; the transverse-longitudinal coupling is not set to zero.
-/

noncomputable section

namespace Maxwell.Continuum.ClusterComplement

open FreeFiber
open scoped InnerProductSpace

theorem bilinearDot_comm (p q : Momentum) : bilinearDot p q = bilinearDot q p := by
  simp [bilinearDot, mul_comm]

theorem bilinearDot_add_right (p q r : Momentum) :
    bilinearDot p (q + r) = bilinearDot p q + bilinearDot p r := by
  simp only [bilinearDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem bilinearDot_smul_right (p q : Momentum) (c : ℂ) :
    bilinearDot p (c • q) = c * bilinearDot p q := by
  simp only [bilinearDot, Pi.smul_apply, smul_eq_mul, mul_left_comm, ← Finset.mul_sum]

theorem bilinearDot_self (p : Momentum) : bilinearDot p p = momentumSquare p := by
  simp only [bilinearDot, momentumSquare, pow_two]

theorem momentumSquare_smul (p : Momentum) (c : ℂ) :
    momentumSquare (c • p) = c ^ 2 * momentumSquare p := by
  simp only [momentumSquare, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]

theorem outer_sandwich (s p : Momentum) :
    momentumOuter s * momentumOuter p * momentumOuter s =
      (bilinearDot s p) ^ 2 • momentumOuter s := by
  simp only [momentumOuter, Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul,
    Matrix.smul_mul, smul_smul]
  change (bilinearDot s p * bilinearDot p s) • momentumOuter s = _
  rw [bilinearDot_comm p s, pow_two]
  rfl

def longitudinalMatrix (s : Momentum) : BlockMatrix := (1 / 3 : ℂ) • momentumOuter s

def longitudinal (s : Fin 3 → ℝ) : Polarization →L[ℂ] Polarization :=
  matrixCLM (longitudinalMatrix (realMomentum s))

theorem longitudinalMatrix_idempotent (s : Momentum) (hs : momentumSquare s = 3) :
    longitudinalMatrix s * longitudinalMatrix s = longitudinalMatrix s := by
  simp only [longitudinalMatrix, Matrix.smul_mul, Matrix.mul_smul, momentumOuter_square,
    hs, smul_smul]
  norm_num

theorem longitudinalMatrix_sandwich (s p : Momentum) (E : ℂ)
    (hs : momentumSquare s = 3) :
    longitudinalMatrix s * blockMatrix p E * longitudinalMatrix s =
      (momentumSquare p - (bilinearDot s p) ^ 2 / 3 - E) • longitudinalMatrix s := by
  simp only [longitudinalMatrix, blockMatrix, mul_sub, sub_mul, Matrix.smul_mul,
    Matrix.mul_smul, mul_one, momentumOuter_square, outer_sandwich, hs, smul_smul]
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

def longitudinalDenominator (s : Fin 3 → ℝ) (q : Momentum) (E : ℂ) : ℂ :=
  momentumSquare q - (bilinearDot (realMomentum s) q) ^ 2 / 3 - E

theorem longitudinal_cancellation (s q : Momentum) (c E : ℂ)
    (hs : momentumSquare s = 3) :
    momentumSquare (c • s + q) - (bilinearDot s (c • s + q)) ^ 2 / 3 - E =
      momentumSquare q - (bilinearDot s q) ^ 2 / 3 - E := by
  rw [momentumSquare_add, momentumSquare_smul, bilinearDot_comm (c • s) q,
    bilinearDot_smul_right, bilinearDot_comm q s, bilinearDot_add_right,
    bilinearDot_smul_right, bilinearDot_self, hs]
  ring

theorem matrixCLM_mul (M N : BlockMatrix) : matrixCLM (M * N) = matrixCLM M * matrixCLM N := by
  apply ContinuousLinearMap.ext
  intro v
  exact (matrixCLM_mul_apply M N v).symm

theorem longitudinal_eq_rankOne (s : Fin 3 → ℝ) :
    longitudinal s = (1 / 3 : ℂ) • InnerProductSpace.rankOne ℂ
      (momentumVector (realMomentum s)) (momentumVector (realMomentum s)) := by
  have hconj : conjugateVector (realMomentum s) = momentumVector (realMomentum s) := by
    ext i
    simp [conjugateVector, momentumVector, realMomentum]
  simp only [longitudinal, longitudinalMatrix, matrixCLM, map_smul]
  change (1 / 3 : ℂ) • matrixCLM (momentumOuter (realMomentum s)) = _
  rw [momentumOuter_rankOne, hconj]

theorem longitudinal_isStarProjection (s : Fin 3 → ℝ)
    (hs : ‖momentumVector (realMomentum s)‖ ^ 2 = 3) : IsStarProjection (longitudinal s) := by
  have hs' : momentumSquare (realMomentum s) = 3 := by rw [momentumSquare_real, hs]; norm_num
  refine ⟨?_, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr ?_⟩
  · change longitudinal s * longitudinal s = longitudinal s
    rw [longitudinal, ← matrixCLM_mul, longitudinalMatrix_idempotent _ hs']
  · intro u v
    change inner ℂ (longitudinal s u) v = inner ℂ u (longitudinal s v)
    rw [longitudinal_eq_rankOne]
    simp only [smul_apply, InnerProductSpace.rankOne_apply, inner_smul_left, inner_smul_right,
      map_div₀, map_one, map_ofNat, inner_conj_symm, mul_comm]

theorem longitudinal_norm_le (s : Fin 3 → ℝ)
    (hs : ‖momentumVector (realMomentum s)‖ ^ 2 = 3) : ‖longitudinal s‖ ≤ 1 :=
  IsStarProjection.norm_le _ (longitudinal_isStarProjection s hs)

theorem transverse_norm_le (s : Fin 3 → ℝ)
    (hs : ‖momentumVector (realMomentum s)‖ ^ 2 = 3) : ‖1 - longitudinal s‖ ≤ 1 :=
  IsStarProjection.norm_le _ (longitudinal_isStarProjection s hs).one_sub

/-- Exact compression at complex momentum, with the corner projection fixed. -/
theorem longitudinal_block_compression (s : Fin 3 → ℝ) (q : Momentum) (c E : ℂ)
    (hs : ‖momentumVector (realMomentum s)‖ ^ 2 = 3) :
    longitudinal s * block (c • realMomentum s + q) E * longitudinal s =
      longitudinalDenominator s q E • longitudinal s := by
  have hs' : momentumSquare (realMomentum s) = 3 := by rw [momentumSquare_real, hs]; norm_num
  rw [longitudinal, block, ← matrixCLM_mul, ← matrixCLM_mul,
    longitudinalMatrix_sandwich _ _ _ hs', longitudinal_cancellation _ _ _ _ hs']
  simp only [matrixCLM, map_smul, longitudinalDenominator]

end Maxwell.Continuum.ClusterComplement
