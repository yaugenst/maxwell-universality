import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-! Summability and exact-index tails of the geometric rate with integer half-frequency. -/

noncomputable section

namespace Maxwell.Continuum.Profile

theorem half_geometric_bound (n : ℕ) : (1/2 : ℝ)^(n/2) ≤ 2*(3/4 : ℝ)^n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num
  | one => norm_num
  | more n hn _ =>
    have he : (n+2)/2=n/2+1 := by omega
    rw [he, pow_succ, pow_add]
    have h := mul_le_mul_of_nonneg_right hn (by norm_num : (0 : ℝ)≤1/2)
    nlinarith only [h, pow_nonneg (by norm_num : (0 : ℝ)≤3/4) n]

theorem half_geometric_summable : Summable (fun n : ℕ => (1/2 : ℝ)^(n/2)) :=
  Summable.of_nonneg_of_le (fun _ => by positivity) half_geometric_bound
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ)≤3/4) (by norm_num : (3/4 : ℝ)<1)).mul_left 2)

theorem half_geometric_tsum : (∑' n : ℕ, (1/2 : ℝ)^(n/2)) ≤ 8 := by
  calc
    _ ≤ ∑' n : ℕ, 2*(3/4 : ℝ)^n := Summable.tsum_le_tsum half_geometric_bound
      half_geometric_summable
      ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ)≤3/4) (by norm_num : (3/4 : ℝ)<1)).mul_left 2)
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num : ‖(3/4 : ℝ)‖<1)]; norm_num

theorem half_geometric_tail (D : ℕ) :
    (∑' n : ℕ, if D≤n then (1/2 : ℝ)^(n/2) else 0) ≤ 8*(1/2 : ℝ)^(D/2) := by
  have hs : Summable (fun n : ℕ => if D≤n then (1/2 : ℝ)^(n/2) else 0) := by
    apply Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) _ half_geometric_summable
    intro n
    split_ifs
    · exact le_rfl
    · positivity
  have he := hs.sum_add_tsum_nat_add D
  have hz : (∑ n ∈ Finset.range D, if D≤n then (1/2 : ℝ)^(n/2) else 0)=0 := by
    apply Finset.sum_eq_zero
    intro n hn
    exact ite_eq_right (not_le_of_gt (Finset.mem_range.mp hn))
  rw [hz, zero_add] at he
  simp only [show ∀ n : ℕ, D≤n+D from fun n => by omega, ↓reduceIte] at he
  rw [← he]
  have hb (n : ℕ) : (1/2 : ℝ)^((n+D)/2) ≤ (1/2 : ℝ)^(D/2)*(1/2 : ℝ)^(n/2) := by
    rw [← pow_add]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  calc
    _ ≤ ∑' n : ℕ, (1/2 : ℝ)^(D/2)*(1/2 : ℝ)^(n/2) :=
      Summable.tsum_le_tsum hb (half_geometric_summable.comp_injective (add_left_injective D))
        (half_geometric_summable.mul_left _)
    _ = (1/2 : ℝ)^(D/2)*(∑' n : ℕ, (1/2 : ℝ)^(n/2)) := tsum_mul_left
    _ ≤ (1/2 : ℝ)^(D/2)*8 := mul_le_mul_of_nonneg_left half_geometric_tsum (by positivity)
    _ = _ := by ring

#print axioms half_geometric_tail

end Maxwell.Continuum.Profile
