import Maxwell.Logical.NormalizationBounds
import Maxwell.Perturbation
import Maxwell.Readout

/-! Actual rounded source and invertibility of its rounded normalized matrix. -/

namespace Maxwell.Logical.Normalization

def roundedSource (S : Source.SparseSystem) (precision : ℕ) : Fin S.n → ℚ :=
  fun i => (Rounding.nearest precision (normalizedSource S i)).value

theorem normalizedSource_norm_le (S : Source.SparseSystem) (hb : S.source ≠ 0) :
    ‖Source.rationalVector (normalizedSource S)‖ ≤ Real.sqrt S.n := by
  simpa using Target.WeightedDecoder.euclidean_norm_le_sqrt_card
    (Source.rationalVector (normalizedSource S)) 1 (by norm_num) (fun i => by
      change |(normalizedSource S i : ℝ)| ≤ 1
      exact_mod_cast normalizedSource_bound S hb i)

theorem roundedSource_error (S : Source.SparseSystem) (precision : ℕ) :
    ‖Source.rationalVector (roundedSource S precision) -
        Source.rationalVector (normalizedSource S)‖ ≤
      Real.sqrt S.n / (2 * 2 ^ precision) := by
  have h := Target.WeightedDecoder.euclidean_norm_le_sqrt_card
    (Source.rationalVector (roundedSource S precision) -
      Source.rationalVector (normalizedSource S)) (1 / (2 * (2 : ℝ) ^ precision))
      (by positivity) (fun i => ?_)
  · simpa [div_eq_mul_inv] using h
  · change |(roundedSource S precision i : ℝ) - (normalizedSource S i : ℝ)| ≤ _
    have hq : ((|(Rounding.nearest precision (normalizedSource S i)).value -
        normalizedSource S i| : ℚ) : ℝ) ≤ ((1 / (2 * (2 : ℚ) ^ precision) : ℚ) : ℝ) :=
      Rat.cast_le.mpr (Rounding.nearest_error precision (normalizedSource S i))
    simpa only [roundedSource, Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_mul,
      Rat.cast_pow, Rat.cast_ofNat, Rat.cast_one] using hq

theorem roundedSource_norm_le (S : Source.SparseSystem) (hb : S.source ≠ 0)
    (precision : ℕ) :
    ‖Source.rationalVector (roundedSource S precision)‖ ≤
      Real.sqrt S.n + Real.sqrt S.n / (2 * 2 ^ precision) := by
  calc
    _ ≤ ‖Source.rationalVector (roundedSource S precision) -
      Source.rationalVector (normalizedSource S)‖ +
      ‖Source.rationalVector (normalizedSource S)‖ := norm_le_norm_sub_add _ _
    _ ≤ _ := by linarith [roundedSource_error S precision, normalizedSource_norm_le S hb]

theorem roundedOperator_unit (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : 0 < S.nnz) (precision : ℕ)
    (hsmall : ((S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S)) *
      ((S.nnz : ℝ) / (2 * 2 ^ precision)) ≤ 1 / 2) :
    ∃ u : (EuclideanSpace ℝ (Fin S.n) →L[ℝ] EuclideanSpace ℝ (Fin S.n))ˣ,
      (u : EuclideanSpace ℝ (Fin S.n) →L[ℝ] EuclideanSpace ℝ (Fin S.n)) =
        roundedOperator S precision ∧
      ‖(↑u⁻¹ : EuclideanSpace ℝ (Fin S.n) →L[ℝ] EuclideanSpace ℝ (Fin S.n))‖ ≤
        2 * (S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S) := by
  obtain ⟨p, _⟩ := Finset.card_pos.mp hm
  let : Nonempty (Fin S.n) := ⟨p.1⟩
  have h := Maxwell.unit_perturbation_inverse_bound (normalizedUnit S hunit hm)
    (roundedOperator S precision - normalizedOperator S) (by
      calc
        _ ≤ ((S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S)) *
            ((S.nnz : ℝ) / (2 * 2 ^ precision)) :=
          mul_le_mul (normalizedUnit_inverse_bound S hunit hm)
            (roundedOperator_error S hunit precision) (norm_nonneg _) (by
              unfold Maxwell.condition₂
              positivity)
        _ ≤ 1 / 2 := hsmall)
  obtain ⟨u, hu, hnorm⟩ := h
  refine ⟨u, ?_, ?_⟩
  · simpa using hu
  · calc
      _ ≤ 2 * ‖(↑((normalizedUnit S hunit hm)⁻¹) :
          EuclideanSpace ℝ (Fin S.n) →L[ℝ] EuclideanSpace ℝ (Fin S.n))‖ := hnorm
      _ ≤ _ := by nlinarith [normalizedUnit_inverse_bound S hunit hm]

end Maxwell.Logical.Normalization
