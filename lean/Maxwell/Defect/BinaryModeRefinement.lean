import Maxwell.Defect.FilterParameters
import Maxwell.Defect.RationalNormalize

/-! Geometric precision bounds for rational power filtering. Both the
matrix accuracy and normalization accuracy use linearly many binary digits. -/
namespace Maxwell.Defect
open InnerProductSpace Module.End Filter Topology

theorem nat_le_two_pow_real (N : ℕ) : (N : ℝ) ≤ 2 ^ N := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      rw [Nat.cast_add, Nat.cast_one, pow_succ]
      have hp : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
      linarith

theorem filter_roundoff_binary (α ε : ℝ) (hα : 1 / 2 ≤ α) (N : ℕ)
    (hε : ε ≤ (1 / 16 : ℝ) ^ N) :
    (N : ℝ) * 2 ^ N * ε ≤ α ^ N * (1 / 2 : ℝ) ^ N := by
  calc
    _ ≤ ((N : ℝ) * 2 ^ N) * (1 / 16 : ℝ) ^ N :=
      mul_le_mul_of_nonneg_left hε (by positivity)
    _ ≤ (2 ^ N * 2 ^ N) * (1 / 16 : ℝ) ^ N := by
      gcongr
      exact nat_le_two_pow_real N
    _ = (1 / 2 : ℝ) ^ N * (1 / 2 : ℝ) ^ N := by
      rw [← mul_pow, ← mul_pow, ← mul_pow]
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by norm_num) hα N) (by positivity)

section Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

set_option maxHeartbeats 600000 in
theorem approximate_modeFilter_scaled_error
    (S : E →L[ℝ] E) (hS : S.toLinearMap.IsSymmetric)
    (target scale μ β ρ : ℝ) (hβ : 0 ≤ β) (hρ : 0 ≤ ρ)
    (hα : 1 / 2 ≤ scalarModeFilter target scale μ)
    (hβα : β ≤ ρ * scalarModeFilter target scale μ)
    (hfilter : ∀ i : Fin (Module.finrank ℝ E), hS.eigenvalues rfl i ≠ μ →
      |scalarModeFilter target scale (hS.eigenvalues rfl i)| ≤ β)
    (hFnorm : ‖modeFilter S target scale‖ ≤ 1)
    (B : E →L[ℝ] E) (hBnorm : ‖B‖ ≤ 2) (N : ℕ)
    (hB : ‖modeFilter S target scale - B‖ ≤ (1 / 16 : ℝ) ^ N)
    (x : E) :
    ‖(B ^ N) x - scalarModeFilter target scale μ ^ N • selectedProjection S μ x‖ ≤
      scalarModeFilter target scale μ ^ N * ((1 / 2 : ℝ) ^ N + ρ ^ N) * ‖x‖ := by
  by_cases hE : Subsingleton E
  · have : (B ^ N) x - scalarModeFilter target scale μ ^ N • selectedProjection S μ x = 0 :=
      Subsingleton.elim _ _
    rw [this, norm_zero]
    positivity
  · have : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    have hpow := norm_power_difference_le (modeFilter S target scale) B hFnorm hBnorm N
    have hround := filter_roundoff_binary (scalarModeFilter target scale μ)
      ‖modeFilter S target scale - B‖ hα N hB
    have hdecay : β ^ N ≤ scalarModeFilter target scale μ ^ N * ρ ^ N := by
      simpa only [mul_pow, mul_comm] using pow_le_pow_left₀ hβ hβα N
    calc
      _ ≤ ‖(B ^ N) x - ((modeFilter S target scale) ^ N) x‖ +
          ‖((modeFilter S target scale) ^ N) x -
            scalarModeFilter target scale μ ^ N • selectedProjection S μ x‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (scalarModeFilter target scale μ ^ N * (1 / 2 : ℝ) ^ N) * ‖x‖ +
          β ^ N * ‖x‖ := by
        apply add_le_add _ (modeFilter_power_error S hS target scale μ β hβ hfilter x N)
        rw [← _root_.sub_apply]
        apply (ContinuousLinearMap.le_opNorm _ _).trans
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        rw [norm_sub_rev]
        exact hpow.trans hround
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hdecay (norm_nonneg x)]

theorem normalized_modeFilter_binary_error
    (S : E →L[ℝ] E) (hS : S.toLinearMap.IsSymmetric)
    (target scale μ β ρ : ℝ) (hβ : 0 ≤ β) (hρ : 0 ≤ ρ)
    (hα : 1 / 2 ≤ scalarModeFilter target scale μ)
    (hβα : β ≤ ρ * scalarModeFilter target scale μ)
    (hfilter : ∀ i : Fin (Module.finrank ℝ E), hS.eigenvalues rfl i ≠ μ →
      |scalarModeFilter target scale (hS.eigenvalues rfl i)| ≤ β)
    (hFnorm : ‖modeFilter S target scale‖ ≤ 1)
    (B : E →L[ℝ] E) (hBnorm : ‖B‖ ≤ 2) (N : ℕ)
    (hB : ‖modeFilter S target scale - B‖ ≤ (1 / 16 : ℝ) ^ N)
    (x : E) (hp : selectedProjection S μ x ≠ 0) :
    ‖NormedSpace.normalize ((B ^ N) x) - NormedSpace.normalize (selectedProjection S μ x)‖ ≤
      (2 * ‖x‖ / ‖selectedProjection S μ x‖) * ((1 / 2 : ℝ) ^ N + ρ ^ N) := by
  have hαpos : 0 < scalarModeFilter target scale μ := lt_of_lt_of_le (by norm_num) hα
  have hαN := pow_pos hαpos N
  have hnonzero : scalarModeFilter target scale μ ^ N • selectedProjection S μ x ≠ 0 :=
    smul_ne_zero hαN.ne' hp
  have he := approximate_modeFilter_scaled_error S hS target scale μ β ρ hβ hρ hα hβα
    hfilter hFnorm B hBnorm N hB x
  have hh := normalize_sub_le ((B ^ N) x)
    (scalarModeFilter target scale μ ^ N • selectedProjection S μ x) hnonzero
  rw [NormedSpace.normalize_smul_of_pos hαN, norm_smul, Real.norm_eq_abs,
    abs_of_pos hαN] at hh
  calc
    _ ≤ 2 * ‖(B ^ N) x - scalarModeFilter target scale μ ^ N • selectedProjection S μ x‖ /
        (scalarModeFilter target scale μ ^ N * ‖selectedProjection S μ x‖) := hh
    _ ≤ 2 * (scalarModeFilter target scale μ ^ N * ((1 / 2 : ℝ) ^ N + ρ ^ N) * ‖x‖) /
        (scalarModeFilter target scale μ ^ N * ‖selectedProjection S μ x‖) := by gcongr
    _ = _ := by field_simp

theorem filteredVector_norm_lower
    (S : E →L[ℝ] E) (hS : S.toLinearMap.IsSymmetric)
    (target scale μ β ρ : ℝ) (hβ : 0 ≤ β) (hρ : 0 ≤ ρ)
    (hα : 1 / 2 ≤ scalarModeFilter target scale μ)
    (hβα : β ≤ ρ * scalarModeFilter target scale μ)
    (hfilter : ∀ i : Fin (Module.finrank ℝ E), hS.eigenvalues rfl i ≠ μ →
      |scalarModeFilter target scale (hS.eigenvalues rfl i)| ≤ β)
    (hFnorm : ‖modeFilter S target scale‖ ≤ 1)
    (B : E →L[ℝ] E) (hBnorm : ‖B‖ ≤ 2) (N : ℕ)
    (hB : ‖modeFilter S target scale - B‖ ≤ (1 / 16 : ℝ) ^ N)
    (x : E) (p : ℝ) (hp : 0 ≤ p) (hproj : p ≤ ‖selectedProjection S μ x‖)
    (hsmall : ((1 / 2 : ℝ) ^ N + ρ ^ N) * ‖x‖ ≤ p / 2) :
    (1 / 2 : ℝ) ^ N * p / 2 ≤ ‖(B ^ N) x‖ := by
  have hαpos : 0 < scalarModeFilter target scale μ := lt_of_lt_of_le (by norm_num) hα
  have hαN := pow_pos hαpos N
  have he := approximate_modeFilter_scaled_error S hS target scale μ β ρ hβ hρ hα hβα
    hfilter hFnorm B hBnorm N hB x
  have ht := norm_le_norm_add_norm_sub ((B ^ N) x)
    (scalarModeFilter target scale μ ^ N • selectedProjection S μ x)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hαN] at ht
  have hpn := mul_le_mul_of_nonneg_left hproj hαN.le
  have hs := mul_le_mul_of_nonneg_left hsmall hαN.le
  have halower := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hα N) hp
  nlinarith

end Operator
end Maxwell.Defect
