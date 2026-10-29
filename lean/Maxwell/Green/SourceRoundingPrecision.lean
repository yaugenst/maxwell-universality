import Maxwell.Green.SourceRounding
import Mathlib.Data.Nat.Log

/-! The executable least dyadic precision equals the explicit integer precision
used by the shared source-mode array producer. -/
namespace Maxwell.Defect.SourceRounding

private theorem power_test (n b p : ℕ) :
    (1 / 2 : ℚ)^p ≤ coordinateBudget n b ↔ (n + 1) * 2^b ≤ 2^p := by
  have hb : (0 : ℚ) < 2^b := by positivity
  have hp : (0 : ℚ) < 2^p := by positivity
  have hn : (0 : ℚ) < n + 1 := by positivity
  rw [coordinateBudget, div_pow, div_pow, one_pow, one_pow, div_div]
  rw [div_le_div_iff₀ hp (mul_pos hb hn)]
  norm_cast
  simp only [one_mul, mul_comm]

private theorem exponent_test (n b p : ℕ) :
    (n + 1) * 2^b ≤ 2^p ↔ b + Nat.clog 2 (n + 1) ≤ p := by
  constructor
  · intro h
    have hb : b ≤ p := by
      apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
      exact (Nat.le_mul_of_pos_left _ (by omega : 0 < n + 1)).trans h
    have hcancel : n + 1 ≤ 2^(p-b) := by
      have he : p = b + (p-b) := by omega
      rw [he, pow_add] at h
      have h' : (n+1)*2^b ≤ 2^(p-b)*2^b := by simpa [mul_comm] using h
      exact (mul_le_mul_iff_left₀ (by positivity : 0 < (2:ℕ)^b)).mp h'
    have hc := Nat.clog_le_of_le_pow hcancel
    omega
  · intro h
    calc
      (n + 1) * 2^b ≤ 2^(Nat.clog 2 (n+1)) * 2^b :=
        Nat.mul_le_mul_right _ (Nat.le_pow_clog (by decide : 1 < 2) _)
      _ = 2^(b + Nat.clog 2 (n+1)) := by rw [pow_add, mul_comm]
      _ ≤ 2^p := Nat.pow_le_pow_right (by decide) h

theorem coordinateBudget_le_one (n b : ℕ) : coordinateBudget n b ≤ 1 := by
  apply (div_le_one (by positivity : (0 : ℚ) < n+1)).mpr
  exact (pow_le_one₀ (by norm_num : (0 : ℚ) ≤ 1/2) (by norm_num)).trans (by exact_mod_cast Nat.le_add_left 1 n)

theorem precisionBits_coordinateBudget (n b : ℕ) :
    Realization.precisionBits (coordinateBudget n b) (coordinateBudget_pos n b) =
      b + Nat.clog 2 (n+1) := by
  unfold Realization.precisionBits Realization.geometricSteps
  apply (Nat.find_eq_iff _).mpr
  have hbudget : Realization.precisionBudget (coordinateBudget n b) = coordinateBudget n b :=
    min_eq_right (coordinateBudget_le_one n b)
  simp only [hbudget, power_test, exponent_test]
  exact ⟨le_rfl, fun p hp => Nat.not_le_of_lt hp⟩

theorem selectedRound_numerator (n b : ℕ) (x : ℚ) :
    (Realization.selectedRound (coordinateBudget n b) (coordinateBudget_pos n b) x).numerator =
      (Logical.Rounding.nearest (b + Nat.clog 2 (n+1)) x).numerator := by
  exact congrArg (fun p => (Logical.Rounding.nearest p x).numerator)
    (precisionBits_coordinateBudget n b)

theorem selectedRound_value (n b : ℕ) (x : ℚ) :
    (Realization.selectedRound (coordinateBudget n b) (coordinateBudget_pos n b) x).value =
      (Logical.Rounding.nearest (b + Nat.clog 2 (n+1)) x).value := by
  exact congrArg (fun p => (Logical.Rounding.nearest p x).value)
    (precisionBits_coordinateBudget n b)

theorem roundedWeightedVector_nearest {n : ℕ} (W : Fin n → ℚ)
    (q : ℕ → Fin n → ℚ) (b : ℕ) (i : Fin n) :
    roundedWeightedVector W q b i =
      (Logical.Rounding.nearest (b + Nat.clog 2 (n+1))
        (DyadicSqrt.weight (W i) (b+2) * q (b+2) i)).value := by
  unfold roundedWeightedVector roundVector
  rw [selectedRound_value]
  rfl

end Maxwell.Defect.SourceRounding
