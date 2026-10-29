import Maxwell.Target
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Maxwell.Target.WeightedDecoder

open scoped BigOperators

/-- The actual emitted rational stencil amplifies finite message error by
its absolute row sum. This is valid for every accurate message. -/
theorem decode_error_le {ι : Type*} {n : ℕ} (D : WeightedDecoder ι n)
    (w : D.Messages) (y : ι → ℝ) (hw : D.Accurate w y) (i : Fin n) :
    |(D.decode w i : ℝ) - D.ideal y i| ≤
      (∑ j ∈ D.support i, |(D.weight i j : ℝ)|) /
        (2 : ℝ) ^ D.format.fractionalBits := by
  rw [D.decode_error_identity]
  calc
    |∑ j ∈ D.support i, (D.weight i j : ℝ) *
        ((D.format.value (w j) : ℝ) - y (D.coordinate j))| ≤
        ∑ j ∈ D.support i, |(D.weight i j : ℝ) *
          ((D.format.value (w j) : ℝ) - y (D.coordinate j))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ D.support i, |(D.weight i j : ℝ)| *
        (1 / (2 : ℝ) ^ D.format.fractionalBits) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hw j) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- A coordinatewise bound controls the true Euclidean norm. -/
theorem euclidean_norm_le_sqrt_card {n : ℕ} (v : EuclideanSpace ℝ (Fin n))
    (ε : ℝ) (hε : 0 ≤ ε) (hv : ∀ i, |v i| ≤ ε) :
    ‖v‖ ≤ Real.sqrt n * ε := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hε)).mp
  rw [EuclideanSpace.norm_sq_eq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
  calc
    ∑ i, ‖v i‖ ^ 2 ≤ ∑ _ : Fin n, ε ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact pow_le_pow_left₀ (norm_nonneg _) (by simpa using hv i) 2
    _ = (n : ℝ) * ε ^ 2 := by simp

/-- Finite local reads yield a bound in the same Euclidean norm used by the
source residual guarantee, with the actual stored rational calibration. -/
theorem decode_euclidean_error_le {ι : Type*} {n : ℕ} (D : WeightedDecoder ι n)
    (w : D.Messages) (y : ι → ℝ) (hw : D.Accurate w y)
    (W : ℝ) (hW : 0 ≤ W)
    (hrow : ∀ i, ∑ j ∈ D.support i, |(D.weight i j : ℝ)| ≤ W) :
    ‖WithLp.toLp 2 (fun i => (D.decode w i : ℝ) - D.ideal y i)‖ ≤
      Real.sqrt n * (W / (2 : ℝ) ^ D.format.fractionalBits) := by
  apply euclidean_norm_le_sqrt_card _ _ (div_nonneg hW (by positivity))
  intro i
  exact (D.decode_error_le w y hw i).trans
    (div_le_div_of_nonneg_right (hrow i) (by positivity))

end Maxwell.Target.WeightedDecoder
