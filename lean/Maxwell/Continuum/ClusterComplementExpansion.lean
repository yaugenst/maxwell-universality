import Maxwell.Continuum.ClusterComplementCoupling

/-!
# Exact transverse compression of the complex Maxwell block

The linear and quadratic momentum terms are separated by matrix identities,
with the projection fixed at the real corner direction.
-/

noncomputable section

namespace Maxwell.Continuum.ClusterComplement

open FreeFiber

def transverseMatrix (s : Momentum) : BlockMatrix := 1 - longitudinalMatrix s

theorem transverseMatrix_idempotent (s : Momentum) (hs : momentumSquare s = 3) :
    transverseMatrix s * transverseMatrix s = transverseMatrix s := by
  simp only [transverseMatrix, mul_sub, sub_mul, one_mul, mul_one,
    longitudinalMatrix_idempotent s hs]
  abel

theorem transverseMatrix_left_outer (s q : Momentum) (hs : momentumSquare s = 3) :
    transverseMatrix s * Matrix.vecMulVec s q = 0 := by
  have hss : dotProduct s s = 3 := by simpa only [dotProduct, momentumSquare, pow_two] using hs
  simp only [transverseMatrix, longitudinalMatrix, momentumOuter, sub_mul, one_mul,
    Matrix.smul_mul, Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul, hss, smul_smul]
  norm_num

theorem transverseMatrix_right_outer (s q : Momentum) (hs : momentumSquare s = 3) :
    Matrix.vecMulVec q s * transverseMatrix s = 0 := by
  have hss : dotProduct s s = 3 := by simpa only [dotProduct, momentumSquare, pow_two] using hs
  simp only [transverseMatrix, longitudinalMatrix, momentumOuter, mul_sub, mul_one,
    Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul, hss, smul_smul]
  norm_num

theorem transverseMatrix_outer_shift (s q : Momentum) (c : ℂ) (hs : momentumSquare s = 3) :
    transverseMatrix s * momentumOuter (c • s + q) * transverseMatrix s =
      transverseMatrix s * momentumOuter q * transverseMatrix s := by
  have hz : transverseMatrix s * Matrix.vecMulVec q s * transverseMatrix s = 0 := by
    rw [mul_assoc, transverseMatrix_right_outer s q hs, mul_zero]
  rw [momentumOuter_add, momentumOuter_smul, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul]
  simp only [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul,
    momentumOuter, transverseMatrix_left_outer s s hs, transverseMatrix_left_outer s q hs,
    smul_zero, zero_add, hz, add_zero]

theorem transverseMatrix_block_expansion (s q : Momentum) (c E : ℂ)
    (hs : momentumSquare s = 3) :
    transverseMatrix s * blockMatrix (c • s + q) E * transverseMatrix s =
      (3 * c ^ 2 - E + 2 * c * bilinearDot s q) • transverseMatrix s +
        transverseMatrix s * blockMatrix q 0 * transverseMatrix s := by
  have hsq : momentumSquare (c • s + q) =
      3 * c ^ 2 + 2 * c * bilinearDot s q + momentumSquare q := by
    rw [momentumSquare_add, momentumSquare_smul, hs, bilinearDot_comm (c • s) q,
      bilinearDot_smul_right, bilinearDot_comm q s]
    ring
  simp only [blockMatrix, mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one,
    transverseMatrix_idempotent s hs, sub_zero, transverseMatrix_outer_shift s q c hs, hsq]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem transverseMatrix_CLM (s : Fin 3 → ℝ) :
    matrixCLM (transverseMatrix (realMomentum s)) = 1 - longitudinal s := by
  rw [transverseMatrix, matrixCLM_sub, matrixCLM_one_eq]
  rfl

theorem transverse_block_expansion (s : Fin 3 → ℝ) (q : Momentum) (c E : ℂ)
    (hs : ‖momentumVector (realMomentum s)‖ ^ 2 = 3) :
    (1 - longitudinal s) * block (c • realMomentum s + q) E * (1 - longitudinal s) =
      (3 * c ^ 2 - E + 2 * c * bilinearDot (realMomentum s) q) • (1 - longitudinal s) +
        (1 - longitudinal s) * block q 0 * (1 - longitudinal s) := by
  have hs' : momentumSquare (realMomentum s) = 3 := by rw [momentumSquare_real, hs]; norm_num
  rw [← transverseMatrix_CLM, block, block, ← matrixCLM_mul, ← matrixCLM_mul,
    ← matrixCLM_mul, ← matrixCLM_mul, transverseMatrix_block_expansion _ _ _ _ hs',
    matrixCLM_add, matrixCLM_smul]

theorem block_smul_zero (q : Momentum) (c : ℂ) : block (c • q) 0 = c ^ 2 • block q 0 := by
  have hm : blockMatrix (c • q) 0 = c ^ 2 • blockMatrix q 0 := by
    simp only [blockMatrix, momentumSquare_smul, momentumOuter_smul, sub_zero, smul_sub, smul_smul]
  rw [block, hm, matrixCLM_smul]
  rfl

end Maxwell.Continuum.ClusterComplement
