import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.Complex.Basic

/-! Finite-order product estimates used by the actual regular symbol.
The conclusion follows from the full Leibniz formula, with one common
bound for each factor's derivatives through the requested order. -/

noncomputable section

namespace Maxwell.Continuum.BoundedLeibniz

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]

theorem mul_derivative_le {f g : 𝕜 → ℂ} {x : 𝕜} {n : ℕ} {A B : ℝ}
    (hA : 0 ≤ A)
    (hf : ContDiffAt 𝕜 n f x) (hg : ContDiffAt 𝕜 n g x)
    (hfb : ∀ i ≤ n, ‖iteratedDeriv i f x‖ ≤ A)
    (hgb : ∀ i ≤ n, ‖iteratedDeriv i g x‖ ≤ B) :
    ‖iteratedDeriv n (fun t => f t*g t) x‖ ≤ (2 : ℝ)^n*A*B := by
  have he := iteratedDerivWithin_mul (s := Set.univ) (x := x) (n := n)
    (Set.mem_univ x) uniqueDiffOn_univ hf.contDiffWithinAt hg.contDiffWithinAt
  simp only [iteratedDerivWithin_univ] at he
  change iteratedDeriv n (fun t => f t*g t) x = _ at he
  rw [he]
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), ‖(n.choose i : ℂ)*iteratedDeriv i f x*iteratedDeriv (n-i) g x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*A*B := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hfb i hin) (Nat.cast_nonneg _))
        (hgb (n-i) (Nat.sub_le _ _)) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hA)
    _ = (∑ i ∈ Finset.range (n+1), (n.choose i : ℝ))*A*B := by
      rw [Finset.sum_mul, Finset.sum_mul]
    _ = _ := by rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]

theorem real_smul_derivative_le {f : ℝ → ℝ} {g : ℝ → ℂ} {x : ℝ} {n : ℕ} {A B : ℝ}
    (hA : 0 ≤ A)
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x)
    (hfb : ∀ i ≤ n, |iteratedDeriv i f x| ≤ A)
    (hgb : ∀ i ≤ n, ‖iteratedDeriv i g x‖ ≤ B) :
    ‖iteratedDeriv n (fun t => f t • g t) x‖ ≤ (2 : ℝ)^n*A*B := by
  have he := iteratedDerivWithin_smul (s := Set.univ) (x := x) (n := n)
    (Set.mem_univ x) uniqueDiffOn_univ hf.contDiffWithinAt hg.contDiffWithinAt
  simp only [iteratedDerivWithin_univ] at he
  change iteratedDeriv n (fun t => f t • g t) x = _ at he
  rw [he]
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), ‖n.choose i • iteratedDeriv i f x • iteratedDeriv (n-i) g x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*A*B := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [← Nat.cast_smul_eq_nsmul ℝ, norm_smul, Real.norm_natCast,
        norm_smul, Real.norm_eq_abs, ← mul_assoc]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hfb i hin) (Nat.cast_nonneg _))
        (hgb (n-i) (Nat.sub_le _ _)) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hA)
    _ = (∑ i ∈ Finset.range (n+1), (n.choose i : ℝ))*A*B := by
      rw [Finset.sum_mul, Finset.sum_mul]
    _ = _ := by rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]

end Maxwell.Continuum.BoundedLeibniz
