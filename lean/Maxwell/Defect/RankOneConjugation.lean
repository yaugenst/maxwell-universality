import Maxwell.Defect.RankOne
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.CStarAlgebra.Basic

/-! A rational orthogonal change of coordinates for first-order block
elimination. The Cayley transform avoids assuming analytic eigenbranches. -/
namespace Maxwell.Defect

open scoped Ring

section Cayley
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

/-- Cayley transform of a small skew-adjoint increment. -/
noncomputable def cayley (Z : R) : R := (1 + Z) * (1 - Z)⁻¹ʳ

omit [NormedAlgebra ℝ R] in
/-- An explicit bound for the Neumann inverse in the half-unit ball. -/
theorem inverse_one_sub_norm_le_two [NormOneClass R] (Z : R) (hZ : ‖Z‖ ≤ 1 / 2) :
    ‖(1 - Z)⁻¹ʳ‖ ≤ 2 := by
  have hlt : ‖Z‖ < 1 := by linarith
  rw [← geom_series_eq_inverse Z hlt]
  have hb := tsum_geometric_le_of_norm_lt_one Z hlt
  rw [norm_one] at hb
  have hi : (1 - ‖Z‖)⁻¹ ≤ (2 : ℝ) := by
    exact inv_le_of_inv_le₀ (by norm_num) (by linarith)
  linarith

/-- Exact quadratic remainder identity for the Cayley transform. -/
theorem cayley_second_order_identity (Z : R) (hZ : ‖Z‖ < 1) :
    cayley Z - 1 - (2 : ℝ) • Z = (2 : ℝ) • (Z * Z * (1 - Z)⁻¹ʳ) := by
  have hcancel := Ring.mul_inverse_cancel (1 - Z) (IsUnit.one_sub_of_norm_lt_one hZ)
  have hinv : (1 - Z)⁻¹ʳ = 1 + Z * (1 - Z)⁻¹ʳ := by
    rw [sub_mul, one_mul] at hcancel
    exact sub_eq_iff_eq_add.mp hcancel
  have hU : cayley Z = 1 + (2 : ℝ) • (Z * (1 - Z)⁻¹ʳ) := by
    unfold cayley
    rw [add_mul, one_mul]
    nth_rw 1 [hinv]
    simp only [two_smul]
    abel
  have hz : Z * (1 - Z)⁻¹ʳ = Z + Z * Z * (1 - Z)⁻¹ʳ := by
    nth_rw 1 [hinv]
    noncomm_ring
  rw [hU, hz, smul_add]
  abel

/-- A uniform, explicit second-order operator bound. -/
theorem cayley_second_order_norm [NormOneClass R] (Z : R) (hZ : ‖Z‖ ≤ 1 / 2) :
    ‖cayley Z - 1 - (2 : ℝ) • Z‖ ≤ 4 * ‖Z‖ ^ 2 := by
  rw [cayley_second_order_identity Z (by linarith)]
  calc
    ‖(2 : ℝ) • (Z * Z * (1 - Z)⁻¹ʳ)‖ = 2 * ‖Z * Z * (1 - Z)⁻¹ʳ‖ := by
      simp [norm_smul]
    _ ≤ 2 * ((‖Z‖ * ‖Z‖) * ‖(1 - Z)⁻¹ʳ‖) := by
      gcongr
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 2 * ((‖Z‖ * ‖Z‖) * 2) := by
      gcongr
      exact inverse_one_sub_norm_le_two Z hZ
    _ = 4 * ‖Z‖ ^ 2 := by ring

theorem cayley_sub_one_norm [NormOneClass R] (Z : R) (hZ : ‖Z‖ ≤ 1 / 2) :
    ‖cayley Z - 1‖ ≤ 4 * ‖Z‖ := by
  have hr := cayley_second_order_norm Z hZ
  have ht := norm_add_le (cayley Z - 1 - (2 : ℝ) • Z) ((2 : ℝ) • Z)
  rw [sub_add_cancel, norm_smul] at ht
  norm_num at ht
  nlinarith [norm_nonneg Z]

variable [StarRing R]

omit [NormedAlgebra ℝ R] in
/-- The Cayley transform is exactly unitary for a skew-adjoint increment. -/
theorem cayley_mem_unitary (Z : R) (hZ : ‖Z‖ < 1) (hskew : star Z = -Z) :
    cayley Z ∈ unitary R := by
  have hden : IsUnit (1 - Z) := IsUnit.one_sub_of_norm_lt_one hZ
  have hnum : IsUnit (1 + Z) := by simpa [hskew] using hden.star
  have hinv : IsUnit ((1 - Z)⁻¹ʳ) := by
    rw [Ring.inverse_of_isUnit hden]
    exact Units.isUnit _
  apply (hnum.mul hinv).mem_unitary_of_star_mul_self
  change star (cayley Z) * cayley Z = 1
  rw [cayley, star_mul, ← Ring.inverse_star, star_sub, star_add, star_one,
    hskew, sub_neg_eq_add, ← sub_eq_add_neg]
  calc
    (1 + Z)⁻¹ʳ * (1 - Z) * ((1 + Z) * (1 - Z)⁻¹ʳ) =
        (1 + Z)⁻¹ʳ * ((1 - Z) * (1 + Z)) * (1 - Z)⁻¹ʳ := by simp [mul_assoc]
    _ = (1 + Z)⁻¹ʳ * ((1 + Z) * (1 - Z)) * (1 - Z)⁻¹ʳ := by
      congr 2
      noncomm_ring
    _ = 1 := by
      rw [← mul_assoc, Ring.inverse_mul_cancel _ hnum, one_mul,
        Ring.mul_inverse_cancel _ hden]

variable [StarModule ℝ R] [NormedStarGroup R]

omit [CompleteSpace R] [StarModule ℝ R] [NormedStarGroup R] in
theorem cayley_conjugation_remainder_identity (S Z : R) (hskew : star Z = -Z) :
    star (cayley Z) * S * cayley Z - S -
        (S * ((2 : ℝ) • Z) - ((2 : ℝ) • Z) * S) =
      star (cayley Z - 1 - (2 : ℝ) • Z) * S + S * (cayley Z - 1 - (2 : ℝ) • Z) +
        star (cayley Z - 1) * S * (cayley Z - 1) := by
  simp only [two_smul, star_sub, star_add, star_one, hskew]
  noncomm_ring

omit [StarModule ℝ R] in
/-- Conjugation by the actual orthogonal Cayley transform has the expected
commutator as its first-order term, with an explicit quadratic norm bound. -/
theorem cayley_conjugation_norm [NormOneClass R] (S Z : R)
    (hZ : ‖Z‖ ≤ 1 / 2) (hskew : star Z = -Z) :
    ‖star (cayley Z) * S * cayley Z - S -
        (S * ((2 : ℝ) • Z) - ((2 : ℝ) • Z) * S)‖ ≤ 24 * ‖S‖ * ‖Z‖ ^ 2 := by
  let P := cayley Z - 1
  let V := cayley Z - 1 - (2 : ℝ) • Z
  have hP : ‖P‖ ≤ 4 * ‖Z‖ := cayley_sub_one_norm Z hZ
  have hV : ‖V‖ ≤ 4 * ‖Z‖ ^ 2 := cayley_second_order_norm Z hZ
  rw [cayley_conjugation_remainder_identity S Z hskew]
  change ‖star V * S + S * V + star P * S * P‖ ≤ _
  have h₁ : ‖star V * S‖ ≤ (4 * ‖Z‖ ^ 2) * ‖S‖ := by
    calc
      _ ≤ ‖star V‖ * ‖S‖ := norm_mul_le _ _
      _ = ‖V‖ * ‖S‖ := by rw [norm_star]
      _ ≤ _ := mul_le_mul_of_nonneg_right hV (norm_nonneg _)
  have h₂ : ‖S * V‖ ≤ ‖S‖ * (4 * ‖Z‖ ^ 2) := by
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left hV (norm_nonneg _))
  have h₃ : ‖star P * S * P‖ ≤ (4 * ‖Z‖) * ‖S‖ * (4 * ‖Z‖) := by
    calc
      _ ≤ (‖star P‖ * ‖S‖) * ‖P‖ :=
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
      _ = (‖P‖ * ‖S‖) * ‖P‖ := by rw [norm_star]
      _ ≤ _ := by gcongr
  calc
    _ ≤ ‖star V * S + S * V‖ + ‖star P * S * P‖ := norm_add_le _ _
    _ ≤ (‖star V * S‖ + ‖S * V‖) + ‖star P * S * P‖ := by
      exact add_le_add (norm_add_le _ _) (le_refl _)
    _ ≤ (4 * ‖Z‖ ^ 2) * ‖S‖ + ‖S‖ * (4 * ‖Z‖ ^ 2) +
        (4 * ‖Z‖) * ‖S‖ * (4 * ‖Z‖) := add_le_add (add_le_add h₁ h₂) h₃
    _ = 24 * ‖S‖ * ‖Z‖ ^ 2 := by ring

omit [CompleteSpace R] [NormedAlgebra ℝ R] [StarRing R] [StarModule ℝ R]
  [NormedStarGroup R] in
private theorem norm_commutator_le (A X : R) :
    ‖A * X - X * A‖ ≤ 2 * ‖A‖ * ‖X‖ := by
  calc
    _ ≤ ‖A * X‖ + ‖X * A‖ := norm_sub_le _ _
    _ ≤ ‖A‖ * ‖X‖ + ‖X‖ * ‖A‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = _ := by ring

/-- The full first-order conjugation statement with a concrete quadratic
remainder constant. The commutator may now be canceled by an algebraically
constructed skew-adjoint off-diagonal block. -/
theorem cayley_first_order_conjugation [NormOneClass R]
    (A B S X : R) (τ C : ℝ) (hτ : 0 ≤ τ) (hτ1 : τ ≤ 1) (hC : 0 ≤ C)
    (hsmall : τ * ‖X‖ ≤ 1) (hX : star X = -X)
    (hrem : ‖S - A - τ • B‖ ≤ C * τ ^ 2) :
    cayley ((τ / 2) • X) ∈ unitary R ∧
      ‖star (cayley ((τ / 2) • X)) * S * cayley ((τ / 2) • X) - A -
        τ • (B + (A * X - X * A))‖ ≤
      (6 * (‖A‖ + ‖B‖ + C) * ‖X‖ ^ 2 + C + 2 * (‖B‖ + C) * ‖X‖) * τ ^ 2 := by
  let Z := (τ / 2) • X
  have hZnorm : ‖Z‖ = (τ / 2) * ‖X‖ := by
    dsimp [Z]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ τ / 2 by positivity)]
  have hZsmall : ‖Z‖ ≤ 1 / 2 := by rw [hZnorm]; nlinarith
  have hZskew : star Z = -Z := by simp [Z, star_smul, hX]
  have htwo : (2 : ℝ) • Z = τ • X := by
    dsimp [Z]
    rw [smul_smul]
    congr 1
    ring
  refine ⟨cayley_mem_unitary Z (by linarith) hZskew, ?_⟩
  have hτsq : τ ^ 2 ≤ τ := by nlinarith
  have hSA : ‖S - A‖ ≤ τ * (‖B‖ + C) := by
    have hh := norm_add_le (S - A - τ • B) (τ • B)
    rw [sub_add_cancel, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ] at hh
    have hc := mul_le_mul_of_nonneg_left hτsq hC
    nlinarith
  have hSnorm : ‖S‖ ≤ ‖A‖ + ‖B‖ + C := by
    have hh := norm_add_le (S - A) A
    rw [sub_add_cancel] at hh
    have hbC : 0 ≤ ‖B‖ + C := add_nonneg (norm_nonneg _) hC
    have hh' := mul_le_mul_of_nonneg_right hτ1 hbC
    nlinarith
  let V := star (cayley Z) * S * cayley Z - S - τ • (S * X - X * S)
  have hV : ‖V‖ ≤ 6 * (‖A‖ + ‖B‖ + C) * ‖X‖ ^ 2 * τ ^ 2 := by
    have hh := cayley_conjugation_norm S Z hZsmall hZskew
    rw [htwo, mul_smul_comm, smul_mul_assoc, ← smul_sub] at hh
    change ‖V‖ ≤ 24 * ‖S‖ * ‖Z‖ ^ 2 at hh
    rw [hZnorm] at hh
    calc
      ‖V‖ ≤ 24 * ‖S‖ * ((τ / 2) * ‖X‖) ^ 2 := hh
      _ ≤ 24 * (‖A‖ + ‖B‖ + C) * ((τ / 2) * ‖X‖) ^ 2 := by gcongr
      _ = _ := by ring
  have hcomm : ‖τ • ((S - A) * X - X * (S - A))‖ ≤
      2 * (‖B‖ + C) * ‖X‖ * τ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ]
    calc
      _ ≤ τ * (2 * ‖S - A‖ * ‖X‖) :=
        mul_le_mul_of_nonneg_left (norm_commutator_le (S - A) X) hτ
      _ ≤ τ * (2 * (τ * (‖B‖ + C)) * ‖X‖) := by gcongr
      _ = _ := by ring
  have hid : star (cayley Z) * S * cayley Z - A - τ • (B + (A * X - X * A)) =
      V + (S - A - τ • B) + τ • ((S - A) * X - X * (S - A)) := by
    dsimp [V]
    simp only [sub_mul, mul_sub, smul_add, smul_sub]
    abel
  change ‖star (cayley Z) * S * cayley Z - A - τ • (B + (A * X - X * A))‖ ≤ _
  rw [hid]
  calc
    _ ≤ ‖V + (S - A - τ • B)‖ + ‖τ • ((S - A) * X - X * (S - A))‖ := norm_add_le _ _
    _ ≤ (‖V‖ + ‖S - A - τ • B‖) + ‖τ • ((S - A) * X - X * (S - A))‖ :=
      add_le_add (norm_add_le _ _) (le_refl _)
    _ ≤ (6 * (‖A‖ + ‖B‖ + C) * ‖X‖ ^ 2 * τ ^ 2 + C * τ ^ 2) +
        2 * (‖B‖ + C) * ‖X‖ * τ ^ 2 := add_le_add (add_le_add hV hrem) hcomm
    _ = _ := by ring

end Cayley
end Maxwell.Defect
