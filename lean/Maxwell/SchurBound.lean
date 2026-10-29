import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

namespace Maxwell

open scoped BigOperators

theorem weighted_sum_square_le {ι : Type*} [Fintype ι] (a x : ι → ℝ) :
    (∑ j, a j * x j) ^ 2 ≤ (∑ j, |a j|) * ∑ j, |a j| * (x j) ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun j _ => abs_nonneg (a j))
    (fun j _ => mul_nonneg (abs_nonneg (a j)) (sq_nonneg (x j)))
  intro j _
  rw [mul_pow]
  have h : |a j| ^ 2 = (a j) ^ 2 := sq_abs _
  nlinarith [sq_nonneg (x j)]

/-- The finite Schur estimate with a common row/column bound. Its constant
does not depend on matrix dimension. -/
theorem matrix_schur_square_bound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hrow : ∀ i, ∑ j, |A i j| ≤ R)
    (hcol : ∀ j, ∑ i, |A i j| ≤ R) (x : κ → ℝ) :
    ∑ i, (A.mulVec x i) ^ 2 ≤ R ^ 2 * ∑ j, (x j) ^ 2 := by
  calc
    ∑ i, (A.mulVec x i) ^ 2 ≤
        ∑ i, (∑ j, |A i j|) * ∑ j, |A i j| * (x j) ^ 2 := by
      exact Finset.sum_le_sum fun i _ => weighted_sum_square_le (A i) x
    _ ≤ ∑ i, R * ∑ j, |A i j| * (x j) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (hrow i)
        (Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
    _ = R * ∑ j, (∑ i, |A i j|) * (x j) ^ 2 := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
    _ ≤ R * ∑ j, R * (x j) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hR
      exact Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _)
    _ = R ^ 2 * ∑ j, (x j) ^ 2 := by
      rw [← Finset.mul_sum]
      ring

/-- Continuous Euclidean action for a rectangular matrix. -/
noncomputable def rectangularEuclideanCLM {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℝ) : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ ι :=
  (Matrix.toEuclideanLin A).toContinuousLinearMap

/-- Separate row and column sums retain the rectangular incidence constant. -/
theorem matrix_schur_square_bound_two {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) (R C : ℝ) (hR : 0 ≤ R)
    (hrow : ∀ i, ∑ j, |A i j| ≤ R)
    (hcol : ∀ j, ∑ i, |A i j| ≤ C) (x : κ → ℝ) :
    ∑ i, (A.mulVec x i) ^ 2 ≤ (R * C) * ∑ j, (x j) ^ 2 := by
  calc
    ∑ i, (A.mulVec x i) ^ 2 ≤
        ∑ i, (∑ j, |A i j|) * ∑ j, |A i j| * (x j) ^ 2 := by
      exact Finset.sum_le_sum fun i _ => weighted_sum_square_le (A i) x
    _ ≤ ∑ i, R * ∑ j, |A i j| * (x j) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (hrow i)
        (Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (sq_nonneg _))
    _ = R * ∑ j, (∑ i, |A i j|) * (x j) ^ 2 := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
    _ ≤ R * ∑ j, C * (x j) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hR
      exact Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; ring

@[simp] theorem rectangularEuclideanCLM_apply {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℝ) (x : EuclideanSpace ℝ κ) (i : ι) :
    rectangularEuclideanCLM A x i = ∑ j, A i j * x j := rfl

/-- The same Schur estimate applies to rectangular incidence operators. -/
theorem rectangularEuclideanCLM_norm_le {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hrow : ∀ i, ∑ j, |A i j| ≤ R)
    (hcol : ∀ j, ∑ i, |A i j| ≤ R) :
    ‖rectangularEuclideanCLM A‖ ≤ R := by
  apply ContinuousLinearMap.opNorm_le_bound _ hR
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hR (norm_nonneg x))).mp
  simp only [EuclideanSpace.real_norm_sq_eq, mul_pow, rectangularEuclideanCLM_apply]
  exact matrix_schur_square_bound A R hR hrow hcol (WithLp.ofLp x)

theorem rectangularEuclideanCLM_norm_le_sqrt {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix ι κ ℝ) (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hrow : ∀ i, ∑ j, |A i j| ≤ R)
    (hcol : ∀ j, ∑ i, |A i j| ≤ C) :
    ‖rectangularEuclideanCLM A‖ ≤ Real.sqrt (R * C) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro x
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg x))).mp
  simp only [mul_pow, Real.sq_sqrt (mul_nonneg hR hC),
    EuclideanSpace.real_norm_sq_eq, rectangularEuclideanCLM_apply]
  exact matrix_schur_square_bound_two A R C hR hrow hcol (WithLp.ofLp x)

/-- A real matrix's Euclidean operator norm is controlled by the common
absolute row and column sum bound. -/
theorem matrix_toEuclideanCLM_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hrow : ∀ i, ∑ j, |A i j| ≤ R)
    (hcol : ∀ j, ∑ i, |A i j| ≤ R) :
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A‖ ≤ R := by
  apply ContinuousLinearMap.opNorm_le_bound _ hR
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hR (norm_nonneg x))).mp
  simpa only [EuclideanSpace.norm_sq_eq, Matrix.ofLp_toEuclideanCLM,
    Real.norm_eq_abs, sq_abs, mul_pow] using
    matrix_schur_square_bound A R hR hrow hcol (WithLp.ofLp x)

theorem symmetric_matrix_toEuclideanCLM_norm_le {ι : Type*}
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) (R : ℝ)
    (hR : 0 ≤ R) (hA : A.IsSymm) (hrow : ∀ i, ∑ j, |A i j| ≤ R) :
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) A‖ ≤ R := by
  apply matrix_toEuclideanCLM_norm_le A R hR hrow
  intro j
  convert hrow j using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [hA.apply i j]

end Maxwell
