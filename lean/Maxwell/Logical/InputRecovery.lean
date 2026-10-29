import Maxwell.Logical.SourceRounding
import Maxwell.Logical.Decoder

/-! Uniform residual transfer through actual input and selected-coordinate rounding. -/

namespace Maxwell.Logical.Normalization

theorem norm_le_inverse_times_residual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : (E →L[ℝ] E)ˣ) (x b : E) :
    ‖x‖ ≤ ‖(↑u⁻¹ : E →L[ℝ] E)‖ * (‖(u : E →L[ℝ] E) x - b‖ + ‖b‖) := by
  have hi : (↑u⁻¹ : E →L[ℝ] E) ((u : E →L[ℝ] E) x) = x := by
    change ((↑u⁻¹ * ↑u : E →L[ℝ] E) x) = x
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rfl
  calc
    ‖x‖ = ‖(↑u⁻¹ : E →L[ℝ] E) ((u : E →L[ℝ] E) x)‖ := by rw [hi]
    _ ≤ ‖(↑u⁻¹ : E →L[ℝ] E)‖ * ‖(u : E →L[ℝ] E) x‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (norm_le_norm_sub_add _ _) (norm_nonneg _)

theorem input_rounding_residual (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : 0 < S.nnz)
    (precision : ℕ) (L eta : ℝ) (hL : 0 < L) (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hK : (S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S) ≤ L)
    (hprecision : (S.nnz : ℝ) / (2 * 2 ^ precision) ≤ eta / (64 * L))
    (z : EuclideanSpace ℝ (Fin S.n))
    (hres : ‖roundedOperator S precision z - Source.rationalVector (normalizedSource S)‖ ≤
      (eta / 16) * ‖Source.rationalVector (normalizedSource S)‖) :
    ‖normalizedOperator S z - Source.rationalVector (normalizedSource S)‖ ≤
      (eta / 8) * ‖Source.rationalVector (normalizedSource S)‖ := by
  let b := Source.rationalVector (normalizedSource S)
  have hsmall : ((S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S)) *
      ((S.nnz : ℝ) / (2 * 2 ^ precision)) ≤ 1 / 2 := by
    calc
      _ ≤ L * (eta / (64 * L)) := mul_le_mul hK hprecision (by positivity) hL.le
      _ = eta / 64 := by field_simp
      _ ≤ 1 / 2 := by linarith
  obtain ⟨u, hu, hnorm⟩ := roundedOperator_unit S hunit hm precision hsmall
  have hnorm' : ‖(↑u⁻¹ : EuclideanSpace ℝ (Fin S.n) →L[ℝ] EuclideanSpace ℝ (Fin S.n))‖ ≤
      2 * L := by nlinarith
  have hz : ‖z‖ ≤ 2 * L * ((eta / 16 + 1) * ‖b‖) := by
    have h := norm_le_inverse_times_residual u z b
    rw [hu] at h
    calc
      ‖z‖ ≤ _ := h
      _ ≤ (2 * L) * ((eta / 16) * ‖b‖ + ‖b‖) :=
        mul_le_mul hnorm' (add_le_add hres (le_refl ‖b‖)) (by positivity) (by positivity)
      _ = _ := by ring
  have herror : ‖normalizedOperator S - roundedOperator S precision‖ ≤ eta / (64 * L) := by
    rw [norm_sub_rev]
    exact (roundedOperator_error S hunit precision).trans hprecision
  have h := Maxwell.residual_perturbation_bound (normalizedOperator S)
    (roundedOperator S precision) z b b
  simp only [sub_self, norm_zero, add_zero] at h
  calc
    _ ≤ ‖roundedOperator S precision z - b‖ +
        ‖normalizedOperator S - roundedOperator S precision‖ * ‖z‖ := h
    _ ≤ (eta / 16) * ‖b‖ + (eta / (64 * L)) *
        (2 * L * ((eta / 16 + 1) * ‖b‖)) :=
      add_le_add hres (mul_le_mul herror hz (norm_nonneg _) (by positivity))
    _ = (eta / 16 + eta / 32 * (eta / 16 + 1)) * ‖b‖ := by
      field_simp
      ring
    _ ≤ (eta / 8) * ‖b‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      nlinarith [mul_nonneg heta (sub_nonneg.mpr heta1)]

theorem coordinate_rounding_error (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : 0 < S.nnz)
    (eta : ℝ) (heta : 0 ≤ eta) (z : EuclideanSpace ℝ (Fin S.n)) (zq : Fin S.n → ℚ)
    (hread : ∀ i, |(zq i : ℝ) - z i| ≤ eta / (16 * S.nnz)) :
    ‖Source.rationalVector zq - z‖ ≤ eta / 16 := by
  have hm1 : (1 : ℝ) ≤ S.nnz := by exact_mod_cast hm
  have hn : (S.n : ℝ) ≤ S.nnz := by exact_mod_cast Source.dimension_le_nnz S hunit
  have hsqrt : Real.sqrt S.n ≤ (S.nnz : ℝ) := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity, by nlinarith⟩
  calc
    _ ≤ Real.sqrt S.n * (eta / (16 * S.nnz)) :=
      Target.WeightedDecoder.euclidean_norm_le_sqrt_card _ _ (by positivity) hread
    _ ≤ (S.nnz : ℝ) * (eta / (16 * S.nnz)) :=
      mul_le_mul_of_nonneg_right hsqrt (by positivity)
    _ = eta / 16 := by field_simp

theorem selected_output_residual (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : 0 < S.nnz) (hb : S.source ≠ 0)
    (precision : ℕ) (L eta : ℝ) (hL : 0 < L) (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hK : (S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S) ≤ L)
    (hprecision : (S.nnz : ℝ) / (2 * 2 ^ precision) ≤ eta / (64 * L))
    (z : EuclideanSpace ℝ (Fin S.n)) (zq : Fin S.n → ℚ)
    (hres : ‖roundedOperator S precision z - Source.rationalVector (normalizedSource S)‖ ≤
      (eta / 16) * ‖Source.rationalVector (normalizedSource S)‖)
    (hread : ∀ i, |(zq i : ℝ) - z i| ≤ eta / (16 * S.nnz)) :
    ‖normalizedOperator S (Source.rationalVector zq) -
        Source.rationalVector (normalizedSource S)‖ ≤
      (eta / 4) * ‖Source.rationalVector (normalizedSource S)‖ := by
  have h := Maxwell.rounded_output_residual_bound (normalizedOperator S) z
    (Source.rationalVector zq) (Source.rationalVector (normalizedSource S))
  have hres' := input_rounding_residual S hunit hm precision L eta hL heta heta1 hK hprecision z hres
  have he := coordinate_rounding_error S hunit hm eta heta z zq hread
  have hn := normalizedOperator_norm_le_one S hunit hm
  have hb1 := normalizedSource_norm_ge_one S hb
  have hp : ‖normalizedOperator S‖ * ‖Source.rationalVector zq - z‖ ≤ eta / 16 := by
    calc
      _ ≤ 1 * (eta / 16) := mul_le_mul hn he (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  nlinarith [mul_nonneg heta (sub_nonneg.mpr hb1)]

theorem normalizedSource_eq (S : Source.SparseSystem) :
    Source.rationalVector (normalizedSource S) = ((sourceScale S : ℝ)⁻¹) • Source.rhs S := by
  ext i
  simp [Source.rationalVector, normalizedSource, Source.rhs, div_eq_mul_inv, mul_comm]

/-- The actual finite rational readout, including normalization reversal,
satisfies the original source residual. All gate/physical residuals may be
arbitrary; only their stated bound on the rounded source system is used. -/
theorem source_output_residual (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : 0 < S.nnz) (hb : S.source ≠ 0)
    (precision : ℕ) (L eta : ℝ) (hL : 0 < L) (heta : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hK : (S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S) ≤ L)
    (hprecision : (S.nnz : ℝ) / (2 * 2 ^ precision) ≤ eta / (64 * L))
    (z : EuclideanSpace ℝ (Fin S.n)) (zq : Fin S.n → ℚ)
    (hres : ‖roundedOperator S precision z - Source.rationalVector (normalizedSource S)‖ ≤
      (eta / 16) * ‖Source.rationalVector (normalizedSource S)‖)
    (hread : ∀ i, |(zq i : ℝ) - z i| ≤ eta / (16 * S.nnz)) :
    Source.ResidualTarget S (eta / 4) (fun i => (sourceScale S / matrixScale S) * zq i) := by
  apply Maxwell.Logical.source_residual_transfer S (matrixScale S) (sourceScale S)
    (sourceScale_pos S hb).ne' zq (eta / 4)
  simpa only [normalizedOperator_eq, normalizedSource_eq] using
    selected_output_residual S hunit hm hb precision L eta hL heta heta1 hK hprecision z zq hres hread

end Maxwell.Logical.Normalization
