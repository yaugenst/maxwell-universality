import Maxwell.Continuum.CornerRoots

/-! An explicit nonzero transverse eigenvector for the selected literal block. -/

noncomputable section
namespace Maxwell.Continuum.Corner

/-- Rationalized form of the three reciprocals in the continuum proof. -/
def topVector : Vec :=
  ![(8 + Real.sqrt 19) / 15, (1 - Real.sqrt 19) / 6, (Real.sqrt 19 - 7) / 10]

def topDiagonal : Vec := ![(7 / 2 : ℝ), 1 / 2, -(3 / 2)]

theorem topVector_reciprocal (i : Fin 3) :
    topVector i = (topDiagonal i - lambdaStar)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 19)
  fin_cases i <;> norm_num [topVector, topDiagonal, lambdaStar] <;> nlinarith

theorem topVector_sum : ∑ i, topVector i = 0 := by
  simp [topVector, Fin.sum_univ_succ]
  ring

theorem topVector_ne_zero : topVector ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  norm_num [topVector] at h0
  linarith [Real.sqrt_nonneg (19 : ℝ)]

/-- This equality is checked against the actual projected matrix. -/
theorem topVector_eigen : (parityBlock selectedParity).mulVec topVector = lambdaStar • topVector := by
  rw [parityBlock, block_explicit]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 19)
  ext i
  fin_cases i <;> norm_num [parityCoefficients, selectedParity, sign, topVector, lambdaStar,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> nlinarith

theorem topVector_normSq : dotProduct topVector topVector = (361 - 28 * Real.sqrt 19) / 225 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 19)
  norm_num [topVector, dotProduct, Fin.sum_univ_succ]
  nlinarith

theorem topVector_normSq_pos : 0 < dotProduct topVector topVector := by
  rw [topVector_normSq]
  linarith [sqrt_nineteen_bounds.2]

def normalizedTopVector : Vec := (Real.sqrt (dotProduct topVector topVector))⁻¹ • topVector

theorem normalizedTopVector_normSq : dotProduct normalizedTopVector normalizedTopVector = 1 := by
  rw [normalizedTopVector, smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul]
  calc
    _ = ((Real.sqrt (dotProduct topVector topVector)) ^ 2)⁻¹ *
        dotProduct topVector topVector := by ring
    _ = 1 := by
      rw [Real.sq_sqrt topVector_normSq_pos.le]
      exact inv_mul_cancel₀ topVector_normSq_pos.ne'

theorem normalizedTopVector_sum : ∑ i, normalizedTopVector i = 0 := by
  simp only [normalizedTopVector, Pi.smul_apply, ← Finset.smul_sum, topVector_sum, smul_zero]

theorem normalizedTopVector_eigen :
    (parityBlock selectedParity).mulVec normalizedTopVector = lambdaStar • normalizedTopVector := by
  rw [normalizedTopVector, Matrix.mulVec_smul, topVector_eigen]
  exact smul_comm _ _ _

end Maxwell.Continuum.Corner
