import Maxwell.Defect.BinaryModeRefinement
import Maxwell.Defect.FilterPerturbation

/-! Executable fixed startup constants and precision schedules for the
mode filter. Requested binary precision enters only linearly. -/
namespace Maxwell.Defect
open Filter Topology

theorem exists_filterInputOffset (C M : ℚ) :
    ∃ k : ℕ, C ≤ 2 ^ k ∧ C * ((2 * M + 1) / M ^ 2) ≤ 2 ^ k := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt
    (max C (C * ((2 * M + 1) / M ^ 2))) (by norm_num : (1 : ℚ) < 2)
  exact ⟨k, ((le_max_left _ _).trans_lt hk).le, ((le_max_right _ _).trans_lt hk).le⟩

def filterInputOffset (C M : ℚ) : ℕ := Nat.find (exists_filterInputOffset C M)

def filterInputPrecision (C M : ℚ) (N : ℕ) : ℕ := 4 * N + filterInputOffset C M

theorem filterInputPrecision_error (C M : ℚ) (N : ℕ) :
    C * (1 / 2 : ℚ) ^ filterInputPrecision C M N ≤ (1 / 16 : ℚ) ^ N ∧
      C * ((2 * M + 1) / M ^ 2) * (1 / 2 : ℚ) ^ filterInputPrecision C M N ≤
        (1 / 16 : ℚ) ^ N := by
  have hk : C ≤ 2 ^ filterInputOffset C M ∧ C * ((2 * M + 1) / M ^ 2) ≤ 2 ^ filterInputOffset C M := Nat.find_spec (exists_filterInputOffset C M)
  have he : (1 / 2 : ℚ) ^ filterInputPrecision C M N =
      (1 / 16 : ℚ) ^ N / 2 ^ filterInputOffset C M := by
    simp only [filterInputPrecision, pow_add, pow_mul, one_div, inv_pow]
    norm_num
    ring
  have hp : (0 : ℚ) < 2 ^ filterInputOffset C M := by positivity
  constructor
  · rw [he]
    have hh := mul_le_mul_of_nonneg_right hk.1
      (show (0 : ℚ) ≤ (1 / 16 : ℚ) ^ N / 2 ^ filterInputOffset C M by positivity)
    exact hh.trans_eq (by field_simp)
  · rw [he]
    have hh := mul_le_mul_of_nonneg_right hk.2
      (show (0 : ℚ) ≤ (1 / 16 : ℚ) ^ N / 2 ^ filterInputOffset C M by positivity)
    exact hh.trans_eq (by field_simp)

section Operator
variable {n : ℕ}

/-- An operator approximation with a binary error bound supplies the
filter at 16^-N accuracy using 4N plus a fixed number of input digits. -/
theorem rationalModeFilter_binary_error
    (S : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (T : ℕ → Matrix (Fin n) (Fin n) ℚ) (C target M : ℚ)
    (hM : 0 < M) (_hC : 0 ≤ C)
    (hnorm : ‖S‖ + |(target : ℝ)| ≤ (M : ℝ))
    (herr : ∀ b, ‖S - rationalOperator (T b)‖ ≤ (C : ℝ) * (1 / 2 : ℝ) ^ b)
    (N : ℕ) :
    ‖modeFilter S target ((M : ℝ) ^ 2)⁻¹ -
      rationalOperator (rationalModeFilter (T (filterInputPrecision C M N)) target ((M ^ 2)⁻¹))‖ ≤
        (1 / 16 : ℝ) ^ N := by
  obtain ⟨hbase, hfilter⟩ := filterInputPrecision_error C M N
  have hbase' : (C : ℝ) * (1 / 2 : ℝ) ^ filterInputPrecision C M N ≤ (1 / 16 : ℝ) ^ N := by
    have hh := (Rat.cast_le (K := ℝ)).2 hbase
    push_cast at hh
    exact hh
  have hfilter' : (C : ℝ) * ((2 * (M : ℝ) + 1) / (M : ℝ) ^ 2) *
      (1 / 2 : ℝ) ^ filterInputPrecision C M N ≤ (1 / 16 : ℝ) ^ N := by
    have hh := (Rat.cast_le (K := ℝ)).2 hfilter
    push_cast at hh
    exact hh
  have hsmall : ‖S - rationalOperator (T (filterInputPrecision C M N))‖ ≤ 1 :=
    ((herr _).trans hbase').trans (pow_le_one₀ (by norm_num) (by norm_num))
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hscale : 0 ≤ ((M : ℝ) ^ 2)⁻¹ := by positivity
  rw [rationalModeFilter_operator]
  push_cast
  have hh := modeFilter_difference S (rationalOperator (T (filterInputPrecision C M N)))
    target ((M : ℝ) ^ 2)⁻¹ M hnorm hsmall
  rw [abs_of_nonneg hscale] at hh
  calc
    _ ≤ ((M : ℝ) ^ 2)⁻¹ * (2 * (M : ℝ) + 1) *
        ‖S - rationalOperator (T (filterInputPrecision C M N))‖ := hh
    _ ≤ ((M : ℝ) ^ 2)⁻¹ * (2 * (M : ℝ) + 1) *
        ((C : ℝ) * (1 / 2 : ℝ) ^ filterInputPrecision C M N) := by gcongr; exact herr _
    _ ≤ _ := by convert hfilter' using 1; ring

end Operator
end Maxwell.Defect
