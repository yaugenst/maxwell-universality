import Maxwell.Spectral.YeeTaylorCoefficients

namespace Maxwell.Spectral.YeeTaylor

open PeriodicYee PrimitiveYee Matrix YeeTaylorCoefficients
noncomputable section

theorem fiberCoefficient_one_hermitian (material : Cell20 → ℝ) (k q : Momentum) :
    (fiberCoefficient material k q 1).IsHermitian := by
  rw [fiberCoefficient_one]
  unfold Matrix.IsHermitian
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, add_comm]

theorem fiberCoefficient_two_hermitian (material : Cell20 → ℝ) (k q : Momentum) :
    (fiberCoefficient material k q 2).IsHermitian := by
  rw [fiberCoefficient_two]
  unfold Matrix.IsHermitian
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  abel

theorem shiftedOperatorCoefficient_selfAdjoint (material : Cell20 → ℝ)
    (k q : Momentum) (E : ℝ) (n : ℕ) (hn : n ≤ 2) :
    IsSelfAdjoint (shiftedOperatorCoefficient material k q E n) := by
  have hm : (shiftedFiberCoefficient material k q E n).IsHermitian := by
    interval_cases n
    · rw [shiftedFiberCoefficient_zero]
      exact (PrimitiveYee.fiber_hermitian material k).sub
        (Matrix.isHermitian_one.smul (show star (E : ℂ) = (E : ℂ) by simp))
    · simpa only [shiftedFiberCoefficient, show (1:ℕ) ≠ 0 by omega, ite_false, sub_zero]
        using fiberCoefficient_one_hermitian material k q
    · simpa only [shiftedFiberCoefficient, show (2:ℕ) ≠ 0 by omega, ite_false, sub_zero]
        using fiberCoefficient_two_hermitian material k q
  change IsSelfAdjoint (Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ)
    (shiftedFiberCoefficient material k q E n))
  exact (show IsSelfAdjoint (shiftedFiberCoefficient material k q E n) from hm).map
    (Matrix.toEuclideanCLM (n := Electric) (𝕜 := ℂ))

end
end Maxwell.Spectral.YeeTaylor
