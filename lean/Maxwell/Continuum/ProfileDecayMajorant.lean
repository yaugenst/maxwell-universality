import Maxwell.Continuum.WellComplex
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! A summable quantitative majorant for the profile and its differentiated series. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Profile

theorem inverse_square_step (x : ℝ) (hx : 0 ≤ x) :
    1/(x+1)^2 ≤ 2/(x+1)-2/(x+2) := by
  have h1 : 0 < x+1 := by positivity
  have h2 : 0 < x+2 := by positivity
  have he : 2/(x+1)-2/(x+2) = 2/((x+1)*(x+2)) := by field_simp; ring
  rw [he]
  apply (div_le_div_iff₀ (sq_pos_of_pos h1) (mul_pos h1 h2)).mpr
  nlinarith

theorem inverse_square_partial (M : ℕ) :
    ∑ n ∈ Finset.range M, (1/((n : ℝ)+1)^2) ≤ 2-2/((M : ℝ)+1) := by
  induction M with
  | zero => norm_num
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have hs := inverse_square_step (M : ℝ) (Nat.cast_nonneg M)
    push_cast
    rw [show (M : ℝ)+1+1=(M : ℝ)+2 by ring]
    linarith

theorem inverse_square_summable : Summable (fun n : ℕ => 1/((n : ℝ)+1)^2) := by
  apply summable_of_sum_range_le (c := 2) (fun n => by positivity)
  intro M
  exact (inverse_square_partial M).trans (sub_le_self _ (by positivity))

theorem inverse_square_tsum : (∑' n : ℕ, 1/((n : ℝ)+1)^2) ≤ 2 := by
  apply Real.tsum_le_of_sum_range_le (fun n => by positivity)
  intro M
  exact (inverse_square_partial M).trans (sub_le_self _ (by positivity))

theorem weighted_exp_inverse_square (n : ℕ) :
    (1+(n : ℝ)^2)*Real.exp (-Real.sqrt n/128) ≤ (2 : ℝ)^80/((n : ℝ)+1)^2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpoly : (1+(n : ℝ)^2)*((n : ℝ)+1)^2 ≤ 8*(n : ℝ)^4 := by
    have h1 : 1+(n : ℝ)^2 ≤ 2*(n : ℝ)^2 := by nlinarith
    have h2 : ((n : ℝ)+1)^2 ≤ 4*(n : ℝ)^2 := by nlinarith
    calc
      _ ≤ (2*(n : ℝ)^2)*(4*(n : ℝ)^2) := mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
      _ = _ := by ring
  have hf := Well.pow_mul_exp_neg_le_factorial (Real.sqrt n/128) (by positivity) 8
  have hs : Real.sqrt (n : ℝ)^8 = (n : ℝ)^4 := by
    rw [show (8 : ℕ)=2*4 by norm_num, pow_mul, Real.sq_sqrt h0]
  have he : -(Real.sqrt (n : ℝ)/128) = -Real.sqrt n/128 := by ring
  rw [div_pow, hs, he] at hf
  norm_num [Nat.factorial] at hf
  apply (le_div_iff₀ (by positivity : 0 < ((n : ℝ)+1)^2)).mpr
  calc
    _ = ((1+(n : ℝ)^2)*((n : ℝ)+1)^2)*Real.exp (-Real.sqrt n/128) := by ring
    _ ≤ (8*(n : ℝ)^4)*Real.exp (-Real.sqrt n/128) :=
      mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    _ ≤ _ := by nlinarith only [hf]

theorem weighted_exp_summable : Summable (fun n : ℕ =>
    (1+(n : ℝ)^2)*Real.exp (-Real.sqrt n/128)) := by
  apply Summable.of_nonneg_of_le (fun n => by positivity) (weighted_exp_inverse_square)
  simpa only [div_eq_mul_inv, one_mul] using inverse_square_summable.mul_left ((2 : ℝ)^80)

theorem weighted_exp_tsum :
    (∑' n : ℕ, (1+(n : ℝ)^2)*Real.exp (-Real.sqrt n/128)) ≤ (2 : ℝ)^81 := by
  have hs : Summable (fun n : ℕ => (2 : ℝ)^80/((n : ℝ)+1)^2) := by
    simpa only [div_eq_mul_inv, one_mul] using inverse_square_summable.mul_left ((2 : ℝ)^80)
  calc
    _ ≤ ∑' n : ℕ, (2 : ℝ)^80/((n : ℝ)+1)^2 :=
      Summable.tsum_le_tsum weighted_exp_inverse_square weighted_exp_summable hs
    _ = (2 : ℝ)^80*(∑' n : ℕ, 1/((n : ℝ)+1)^2) := by
      simp only [div_eq_mul_inv, one_mul, tsum_mul_left]
    _ ≤ (2 : ℝ)^80*2 := mul_le_mul_of_nonneg_left inverse_square_tsum (by positivity)
    _ = _ := by norm_num

theorem exp_sqrt_split {x D : ℝ} (hD : D ≤ x) :
    Real.exp (-Real.sqrt x/64) ≤ Real.exp (-Real.sqrt D/128)*Real.exp (-Real.sqrt x/128) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have := Real.sqrt_le_sqrt hD
  linarith

theorem weighted_exp_tail (D : ℕ) :
    (∑' n : ℕ, if D ≤ n then (1+(n : ℝ)^2)*Real.exp (-Real.sqrt n/64) else 0) ≤
      (2 : ℝ)^81*Real.exp (-Real.sqrt D/128) := by
  have hmajor (n : ℕ) : (if D ≤ n then (1+(n : ℝ)^2)*Real.exp (-Real.sqrt n/64) else 0) ≤
      Real.exp (-Real.sqrt D/128)*((1+(n : ℝ)^2)*Real.exp (-Real.sqrt n/128)) := by
    split_ifs with hn
    · calc
        _ ≤ (1+(n : ℝ)^2)*(Real.exp (-Real.sqrt D/128)*Real.exp (-Real.sqrt n/128)) :=
          mul_le_mul_of_nonneg_left (exp_sqrt_split (by exact_mod_cast hn)) (by positivity)
        _ = _ := by ring
    · positivity
  have hs := weighted_exp_summable.mul_left (Real.exp (-Real.sqrt D/128))
  have ht : Summable (fun n : ℕ => if D ≤ n then (1+(n : ℝ)^2)*Real.exp (-Real.sqrt n/64) else 0) :=
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity) hmajor hs
  calc
    _ ≤ ∑' n : ℕ, Real.exp (-Real.sqrt D/128)*((1+(n : ℝ)^2)*Real.exp (-Real.sqrt n/128)) :=
      Summable.tsum_le_tsum hmajor ht hs
    _ = Real.exp (-Real.sqrt D/128)*(∑' n : ℕ, (1+(n : ℝ)^2)*Real.exp (-Real.sqrt n/128)) := tsum_mul_left
    _ ≤ Real.exp (-Real.sqrt D/128)*(2 : ℝ)^81 := mul_le_mul_of_nonneg_left weighted_exp_tsum (Real.exp_pos _).le
    _ = _ := by ring

#print axioms weighted_exp_tail

end Maxwell.Continuum.Profile
