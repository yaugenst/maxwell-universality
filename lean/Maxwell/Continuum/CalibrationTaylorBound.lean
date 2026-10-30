import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-! A finite Taylor order with an explicit dyadic error. The order is
polynomial in the magnitude bound and requested number of bits; no
search for a numerically observed remainder is used. -/

namespace Maxwell.Continuum.Calibration

def taylorHalfOrder (B N : ℕ) : ℕ := 4*B^2+N+4

def taylorOrder (B N : ℕ) : ℕ := 2*taylorHalfOrder B N

theorem factorial_double_lower (K : ℕ) :
    (K : ℝ)^K ≤ ((2*K).factorial : ℝ) := by
  have h : K^K ≤ (2*K).factorial := by
    calc
      K^K ≤ (K+1)^K := Nat.pow_le_pow_left (Nat.le_succ K) K
      _ ≤ K.factorial*(K+1)^K := Nat.le_mul_of_pos_left _ (Nat.factorial_pos _)
      _ ≤ (K+K).factorial := Nat.factorial_mul_pow_le_factorial
      _ = _ := by congr 1; omega
  exact_mod_cast h

theorem taylor_remainder_bound (B N : ℕ) {z : ℂ} (hz : ‖z‖ ≤ B) :
    ‖Complex.exp z-∑ k ∈ Finset.range (taylorOrder B N), z^k/(k.factorial : ℂ)‖ ≤
      (1/2 : ℝ)^N := by
  let K := taylorHalfOrder B N
  have hK : 0 < (K : ℝ) := by
    dsimp [K,taylorHalfOrder]
    positivity
  have hKB : 4*(B : ℝ)^2+4 ≤ (K : ℝ) := by
    dsimp [K,taylorHalfOrder]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have hKN : N+1 ≤ K := by dsimp [K,taylorHalfOrder]; omega
  have hbK : (B : ℝ) ≤ K := by nlinarith [sq_nonneg ((B : ℝ)-1)]
  have hexp : ‖z‖/((2*K).succ : ℝ) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    push_cast
    linarith
  have hmain := Complex.exp_bound' hexp
  change ‖Complex.exp z-∑ k ∈ Finset.range (2*K), z^k/(k.factorial : ℂ)‖ ≤ _
  apply hmain.trans
  have hratio : (B : ℝ)^2/(K : ℝ) ≤ 1/4 := by
    apply (div_le_iff₀ hK).mpr
    linarith
  have hterm : ‖z‖^(2*K)/((2*K).factorial : ℝ) ≤ (1/4 : ℝ)^K := by
    calc
      _ ≤ (B : ℝ)^(2*K)/((K : ℝ)^K) :=
        div_le_div₀ (by positivity) (pow_le_pow_left₀ (norm_nonneg _) hz _)
          (by positivity) (factorial_double_lower K)
      _ = ((B : ℝ)^2/(K : ℝ))^K := by rw [div_pow,pow_mul]
      _ ≤ _ := pow_le_pow_left₀ (by positivity) hratio _
  calc
    _ ≤ (1/4 : ℝ)^K*2 := mul_le_mul_of_nonneg_right hterm (by norm_num)
    _ ≤ (1/2 : ℝ)^K*2 := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/4) (by norm_num) K) (by norm_num)
    _ ≤ (1/2 : ℝ)^(N+1)*2 := mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num) hKN)
      (by norm_num)
    _ = _ := by rw [pow_succ]; ring

#print axioms taylor_remainder_bound

end Maxwell.Continuum.Calibration
