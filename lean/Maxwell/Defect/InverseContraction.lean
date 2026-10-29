import Maxwell.Defect.InversePolynomial
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric

/-! The inverse-polynomial contraction is derived from the actual spectral
gap by isometric continuous functional calculus. -/
namespace Maxwell.Defect

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

/-- A self-adjoint spectral gap supplies the inverse and its norm bound. -/
theorem inverse_norm_of_spectral_gap (H : A) (hH : IsSelfAdjoint H)
    (δ : ℝ) (hδ : 0 < δ) (hgap : ∀ x ∈ spectrum ℝ H, δ ≤ |x|) :
    IsUnit H ∧ ‖Ring.inverse H‖ ≤ δ⁻¹ := by
  have hnonzero : ∀ x ∈ spectrum ℝ H, x ≠ 0 := by
    intro x hx hz
    have hh := hgap x hx
    rw [hz, abs_zero] at hh
    linarith
  have hunit : IsUnit H := (spectrum.zero_notMem_iff ℝ).mp
    (fun hz => hnonzero 0 hz rfl)
  refine ⟨hunit, ?_⟩
  have hid : cfc (fun x : ℝ => x⁻¹) H = Ring.inverse H := by
    rw [show (fun x : ℝ => x⁻¹) = (fun x => (id x)⁻¹) from rfl,
      cfc_inv id H hnonzero, cfc_id ℝ H hH]
  rw [← hid]
  apply norm_cfc_le (inv_pos.mpr hδ).le
  intro x hx
  rw [Real.norm_eq_abs, abs_inv]
  exact inv_anti₀ hδ (hgap x hx)

/-- The contraction factor is the exact manuscript value
`1−δ²/M²`, derived from a norm bound and a two-sided spectral gap. -/
theorem inversePolynomial_contraction (H : A) (hH : IsSelfAdjoint H)
    (δ M : ℝ) (hδ : 0 < δ) (hM : 0 < M) (hδM : δ ≤ M)
    (hnorm : ‖H‖ ≤ M) (hgap : ∀ x ∈ spectrum ℝ H, δ ≤ |x|) :
    ‖1 - (M ^ 2)⁻¹ • H ^ 2‖ ≤ 1 - δ ^ 2 / M ^ 2 := by
  have hM2 : 0 < M ^ 2 := sq_pos_of_pos hM
  have hδ2M : δ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hδ.le hδM 2
  have hr : 0 ≤ 1 - δ ^ 2 / M ^ 2 := by
    have := (div_le_one hM2).mpr hδ2M
    linarith
  have hid : cfc (fun x : ℝ => 1 - (M ^ 2)⁻¹ * x ^ 2) H =
      1 - (M ^ 2)⁻¹ • H ^ 2 := by
    rw [cfc_sub (fun _ => 1) (fun x : ℝ => (M ^ 2)⁻¹ * x ^ 2) H,
      cfc_const 1 H hH, map_one, cfc_const_mul (M ^ 2)⁻¹ (fun x : ℝ => x ^ 2) H,
      show (fun x : ℝ => x ^ 2) = (fun x => id x ^ 2) from rfl,
      cfc_pow id 2 H (ha := hH), cfc_id ℝ H hH]
  rw [← hid]
  apply norm_cfc_le hr
  intro x hx
  have hxM : |x| ≤ M :=
    (IsometricContinuousFunctionalCalculus.norm_spectrum_le H hx hH).trans hnorm
  have hxδ := hgap x hx
  have hx2 : x ^ 2 ≤ M ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
  have hδ2 : δ ^ 2 ≤ x ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
  have hxle : (M ^ 2)⁻¹ * x ^ 2 ≤ 1 := by
    rw [← div_eq_inv_mul]
    exact (div_le_one hM2).mpr hx2
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hh := mul_le_mul_of_nonneg_left hδ2 (inv_pos.mpr hM2).le
  rw [div_eq_inv_mul]
  linarith

/-- The explicit rational-friendly contraction factor is nonnegative and
strictly below one whenever the spectral enclosure has positive gap. -/
theorem inversePolynomial_factor_range {δ M : ℝ} (hδ : 0 < δ) (hM : 0 < M)
    (hδM : δ ≤ M) : 0 ≤ 1 - δ ^ 2 / M ^ 2 ∧ 1 - δ ^ 2 / M ^ 2 < 1 := by
  have hM2 := sq_pos_of_pos hM
  have hδ2 := sq_pos_of_pos hδ
  constructor
  · have hh := (div_le_one hM2).mpr (pow_le_pow_left₀ hδ.le hδM 2)
    linarith
  · have := div_pos hδ2 hM2
    linarith

/-- Fully discharged inverse-polynomial enclosure: only the operator's
self-adjointness, spectral gap, and norm enclosure are premises. -/
theorem inversePolynomial_spectral_error [NormOneClass A]
    (H : A) (hH : IsSelfAdjoint H) (δ M : ℝ) (N : ℕ)
    (hδ : 0 < δ) (hM : 0 < M) (hδM : δ ≤ M)
    (hnorm : ‖H‖ ≤ M) (hgap : ∀ x ∈ spectrum ℝ H, δ ≤ |x|) :
    ‖Ring.inverse H - inversePolynomial H (M ^ 2)⁻¹ N‖ ≤
      δ⁻¹ * (1 - δ ^ 2 / M ^ 2) ^ (N + 1) := by
  obtain ⟨hunit, hinv⟩ := inverse_norm_of_spectral_gap H hH δ hδ hgap
  exact inversePolynomial_error_bound H (Ring.inverse H) (M ^ 2)⁻¹ N
    (Ring.inverse_mul_cancel H hunit) hδ hinv
    (inversePolynomial_contraction H hH δ M hδ hM hδM hnorm hgap)

/-- A finite polynomial degree exists for every positive requested
precision at an actual self-adjoint spectral gap. -/
theorem exists_inversePolynomial_spectral_precision [NormOneClass A]
    (H : A) (hH : IsSelfAdjoint H) (δ M ε : ℝ)
    (hδ : 0 < δ) (hM : 0 < M) (hδM : δ ≤ M) (hε : 0 < ε)
    (hnorm : ‖H‖ ≤ M) (hgap : ∀ x ∈ spectrum ℝ H, δ ≤ |x|) :
    ∃ N, ‖Ring.inverse H - inversePolynomial H (M ^ 2)⁻¹ N‖ < ε := by
  obtain ⟨hunit, hinv⟩ := inverse_norm_of_spectral_gap H hH δ hδ hgap
  obtain ⟨hr, hr1⟩ := inversePolynomial_factor_range hδ hM hδM
  exact exists_inversePolynomial_precision H (Ring.inverse H) (M ^ 2)⁻¹
    (Ring.inverse_mul_cancel H hunit) hδ hr hr1 hε hinv
    (inversePolynomial_contraction H hH δ M hδ hM hδM hnorm hgap)

end Maxwell.Defect
