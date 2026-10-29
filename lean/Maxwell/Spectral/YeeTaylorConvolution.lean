import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! The absolutely convergent adjoint-product Taylor series and its sharp
coefficient envelope.  The hypotheses concern the curl coefficients themselves;
no bound on the final Maxwell coefficients is assumed. -/
namespace Maxwell.Spectral.YeeTaylorConvolution

open scoped BigOperators
open Finset Nat

noncomputable section

/-- The Cauchy coefficient of the adjoint-product of a Taylor series. -/
def coefficient {R : Type*} [Semiring R] [Star R] (C : ℕ → R) (n : ℕ) : R :=
  ∑ p ∈ Finset.antidiagonal n, star (C p.1) * C p.2

/-- The scalar exponential coefficients obey the binomial convolution identity. -/
theorem factorial_convolution (a : ℝ) (n : ℕ) :
    (∑ p ∈ Finset.antidiagonal n,
      (a ^ p.1 / (p.1.factorial : ℝ)) * (a ^ p.2 / (p.2.factorial : ℝ))) =
      2 ^ n * a ^ n / (n.factorial : ℝ) := by
  have hb := (Commute.refl a).add_pow' n
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  calc
    _ = (∑ p ∈ Finset.antidiagonal n,
        (n.choose p.1 : ℝ) * (a ^ p.1 * a ^ p.2)) / (n.factorial : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p hp
      have he : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
      rw [← he, Nat.cast_add_choose]
      field_simp
    _ = (a + a) ^ n / (n.factorial : ℝ) := by simpa only [nsmul_eq_mul] using congrArg (fun x : ℝ => x / (n.factorial : ℝ)) hb.symm
    _ = _ := by rw [← two_mul, mul_pow]

section Normed

variable {R : Type*} [NormedRing R] [StarRing R] [NormedStarGroup R]

omit [StarRing R] [NormedStarGroup R] in
/-- Positive-degree exponential envelopes imply absolute convergence, independently
of the constant coefficient. -/
theorem summable_norm (C : ℕ → R) (a : ℝ)
    (hpos : ∀ n, 1 ≤ n → ‖C n‖ ≤ 2 * a ^ n / (n.factorial : ℝ)) :
    Summable (fun n => ‖C n‖) := by
  apply ((NormedSpace.expSeries_div_summable a).mul_left 2).of_norm_bounded_eventually_nat
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  simpa only [norm_norm, mul_div_assoc] using hpos n hn

/-- Absolute convergence permits genuine Cauchy multiplication, including for
noncommuting operator coefficients. -/
theorem coefficient_hasSum [CompleteSpace R] (C : ℕ → R) (S : R)
    (hC : HasSum C S) (hnorm : Summable (fun n => ‖C n‖)) :
    HasSum (coefficient C) (star S * S) := by
  have hstar : Summable (fun n => ‖star (C n)‖) := by simpa using hnorm
  have hsum := summable_norm_sum_mul_antidiagonal_of_summable_norm hstar hnorm
  have he := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hstar hnorm
  rw [hC.tsum_eq, hC.star.tsum_eq] at he
  exact he ▸ hsum.of_norm.hasSum

/-- Retaining the improved constant coefficient only changes the two endpoint
terms of each positive-degree convolution. -/
theorem norm_coefficient_le_sharp (C : ℕ → R) (a b : ℝ) (ha : 0 ≤ a)
    (h0 : ‖C 0‖ ≤ b)
    (hpos : ∀ n, 1 ≤ n → ‖C n‖ ≤ 2 * a ^ n / (n.factorial : ℝ))
    (n : ℕ) (hn : 1 ≤ n) :
    ‖coefficient C n‖ ≤ (4 * 2 ^ n + 4 * b - 8) * a ^ n / (n.factorial : ℝ) := by
  have hn0 : n ≠ 0 := by omega
  have hb : 0 ≤ b := (norm_nonneg _).trans h0
  have hterm : ∀ p ∈ Finset.antidiagonal n,
      ‖C p.1‖ * ‖C p.2‖ ≤
        4 * (a ^ p.1 / (p.1.factorial : ℝ)) * (a ^ p.2 / (p.2.factorial : ℝ)) +
          (if p = (0, n) then (2 * b - 4) * a ^ n / (n.factorial : ℝ) else 0) +
          (if p = (n, 0) then (2 * b - 4) * a ^ n / (n.factorial : ℝ) else 0) := by
    rintro ⟨p, q⟩ hp
    have he : p + q = n := Finset.mem_antidiagonal.mp hp
    by_cases hp0 : p = 0
    · subst p
      simp only [Nat.zero_add] at he
      subst q
      have h := mul_le_mul h0 (hpos n hn) (norm_nonneg _) hb
      simp [hn0, Ne.symm hn0]
      convert h using 1
      ring
    · by_cases hq0 : q = 0
      · subst q
        simp only [Nat.add_zero] at he
        subst p
        have h := mul_le_mul (hpos n hn) h0 (norm_nonneg _) (by positivity)
        simp [hn0]
        convert h using 1
        ring
      · have hp1 : 1 ≤ p := by omega
        have hq1 : 1 ≤ q := by omega
        have h := mul_le_mul (hpos p hp1) (hpos q hq1) (norm_nonneg _) (by positivity)
        have hpn : (p, q) ≠ (0, n) := by simp [hp0]
        have hqn : (p, q) ≠ (n, 0) := by simp [hq0]
        simp only [hpn, hqn, ite_false, add_zero]
        convert h using 1
        ring
  calc
    ‖coefficient C n‖ ≤ ∑ p ∈ Finset.antidiagonal n, ‖C p.1‖ * ‖C p.2‖ := by
      unfold coefficient
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
      simpa only [norm_star] using norm_mul_le (star (C p.1)) (C p.2)
    _ ≤ ∑ p ∈ Finset.antidiagonal n,
        (4 * (a ^ p.1 / (p.1.factorial : ℝ)) * (a ^ p.2 / (p.2.factorial : ℝ)) +
          (if p = (0, n) then (2 * b - 4) * a ^ n / (n.factorial : ℝ) else 0) +
          (if p = (n, 0) then (2 * b - 4) * a ^ n / (n.factorial : ℝ) else 0)) :=
      Finset.sum_le_sum hterm
    _ = 4 * (2 ^ n * a ^ n / (n.factorial : ℝ)) +
        2 * ((2 * b - 4) * a ^ n / (n.factorial : ℝ)) := by
      simp only [Finset.sum_add_distrib]
      simp only [mul_assoc, ← Finset.mul_sum, factorial_convolution]
      simp
      ring
    _ = _ := by ring

/-- The paper's uniform Maxwell coefficient bound, with the exact endpoint
correction bounded by six. -/
theorem norm_coefficient_le (C : ℕ → R) (a : ℝ) (ha : 0 ≤ a)
    (h0 : ‖C 0‖ ≤ 2 * Real.sqrt 3)
    (hpos : ∀ n, 1 ≤ n → ‖C n‖ ≤ 2 * a ^ n / (n.factorial : ℝ))
    (n : ℕ) (hn : 1 ≤ n) :
    ‖coefficient C n‖ ≤ (4 * 2 ^ n + 6) * a ^ n / (n.factorial : ℝ) := by
  refine (norm_coefficient_le_sharp C a (2 * Real.sqrt 3) ha h0 hpos n hn).trans ?_
  have hs : Real.sqrt 3 ≤ (7 : ℝ) / 4 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg (3 : ℝ)]
  gcongr
  linarith

/-- The positive-degree curl bound supplies every convergence hypothesis needed
to identify the complete Maxwell Taylor series. -/
theorem coefficient_hasSum_of_bound [CompleteSpace R] (C : ℕ → R) (S : R) (a : ℝ)
    (hC : HasSum C S)
    (hpos : ∀ n, 1 ≤ n → ‖C n‖ ≤ 2 * a ^ n / (n.factorial : ℝ)) :
    HasSum (coefficient C) (star S * S) :=
  coefficient_hasSum C S hC (summable_norm C a hpos)

/-- The adjoint-product coefficient series converges absolutely. -/
theorem coefficient_summable_norm (C : ℕ → R) (a : ℝ)
    (hpos : ∀ n, 1 ≤ n → ‖C n‖ ≤ 2 * a ^ n / (n.factorial : ℝ)) :
    Summable (fun n => ‖coefficient C n‖) := by
  have hnorm : Summable (fun n => ‖C n‖) := summable_norm C a hpos
  have hstar : Summable (fun n => ‖star (C n)‖) := by simpa only [norm_star] using hnorm
  simpa only [coefficient] using
    (summable_norm_sum_mul_antidiagonal_of_summable_norm
      (f := fun n => star (C n)) (g := C) hstar hnorm)

end Normed

end
end Maxwell.Spectral.YeeTaylorConvolution
