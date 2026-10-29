import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Whole-vector source rounding on the complete emitted support.
The support count is global, rather than the size of one local stencil. -/

namespace Maxwell.Composition

open scoped BigOperators

theorem supported_euclidean_error_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : EuclideanSpace ℝ ι) (support : Finset ι) (h : ℝ)
    (hzero : ∀ i, i ∉ support → x i = 0)
    (herror : ∀ i ∈ support, |x i| ≤ h) :
    ‖x‖ ≤ (support.card : ℝ) * h := by
  have hx : x = ∑ i ∈ support, EuclideanSpace.single i (x i) := by
    ext i
    by_cases hi : i ∈ support
    · simp [hi]
    · simp [hi, hzero i hi]
  calc
    ‖x‖ = ‖∑ i ∈ support, EuclideanSpace.single i (x i)‖ := congrArg norm hx
    _ ≤ ∑ i ∈ support, ‖EuclideanSpace.single i (x i)‖ := norm_sum_le _ _
    _ = ∑ i ∈ support, |x i| := by
      apply Finset.sum_congr rfl
      intro i _
      exact PiLp.norm_single 2 (fun _ : ι => ℝ) i (x i)
    _ ≤ ∑ _i ∈ support, h := Finset.sum_le_sum herror
    _ = (support.card : ℝ) * h := by simp

/-- The stated coordinate grid controls the complete source error.
The `max 1 card` convention includes an empty source support. -/
theorem source_rounding_budget {ι : Type*} [Fintype ι] [DecidableEq ι]
    (fhat f : EuclideanSpace ℝ ι) (support : Finset ι)
    (α ε G L : ℝ) (hα : 0 ≤ α) (hε : 0 ≤ ε) (hG : 1 ≤ G) (hL : 0 < L)
    (hzero : ∀ i, i ∉ support → fhat i = f i)
    (herror : ∀ i ∈ support,
      |fhat i - f i| ≤ α * ε / (32768 * L * max 1 (support.card : ℝ))) :
    ‖fhat - f‖ ≤ α * ε * G / (32768 * L) := by
  have hmax : 0 < max 1 (support.card : ℝ) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hratio : (support.card : ℝ) / max 1 (support.card : ℝ) ≤ 1 :=
    (div_le_one hmax).mpr (le_max_right _ _)
  have hp : 0 ≤ α * ε / (32768 * L) := by positivity
  calc
    _ ≤ (support.card : ℝ) * (α * ε / (32768 * L * max 1 (support.card : ℝ))) :=
      supported_euclidean_error_le (fhat - f) support _
        (fun i hi => sub_eq_zero.mpr (hzero i hi)) herror
    _ = (α * ε / (32768 * L)) *
        ((support.card : ℝ) / max 1 (support.card : ℝ)) := by ring
    _ ≤ (α * ε / (32768 * L)) * 1 := mul_le_mul_of_nonneg_left hratio hp
    _ ≤ (α * ε / (32768 * L)) * G := mul_le_mul_of_nonneg_left hG hp
    _ = α * ε * G / (32768 * L) := by ring

end Maxwell.Composition
