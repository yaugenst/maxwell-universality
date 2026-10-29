import Maxwell.Logical.Normalization
import Maxwell.SchurBound

/-! Euclidean bounds for the actual source normalization. -/

namespace Maxwell.Logical.Normalization

theorem magnitudeMax_attained (qs : List ℚ) (h : 0 < magnitudeMax qs) :
    ∃ q ∈ qs, |q| = magnitudeMax qs := by
  induction qs with
  | nil => simp [magnitudeMax] at h
  | cons q qs ih =>
      by_cases hq : |q| ≤ magnitudeMax qs
      · rw [magnitudeMax, max_eq_right hq] at h ⊢
        obtain ⟨r, hr, he⟩ := ih h
        exact ⟨r, List.mem_cons_of_mem q hr, he⟩
      · exact ⟨q, List.mem_cons_self, (max_eq_left (le_of_not_ge hq)).symm⟩

theorem sourceScale_attained (S : Source.SparseSystem) (hb : S.source ≠ 0) :
    ∃ i, |S.source i| = sourceScale S := by
  obtain ⟨q, hq, he⟩ := magnitudeMax_attained (List.ofFn S.source) (sourceScale_pos S hb)
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
  exact ⟨i, he⟩

theorem normalizedSource_norm_ge_one (S : Source.SparseSystem) (hb : S.source ≠ 0) :
    1 ≤ ‖Source.rationalVector (normalizedSource S)‖ := by
  obtain ⟨i, hi⟩ := sourceScale_attained S hb
  have hcoord : |normalizedSource S i| = 1 := by
    rw [normalizedSource, abs_div, hi, abs_of_pos (sourceScale_pos S hb)]
    exact div_self (sourceScale_pos S hb).ne'
  have h := PiLp.norm_apply_le (Source.rationalVector (normalizedSource S)) i
  have hreal : ‖Source.rationalVector (normalizedSource S) i‖ = 1 := by
    change |((normalizedSource S i : ℚ) : ℝ)| = 1
    exact_mod_cast hcoord
  rwa [hreal] at h

noncomputable def normalizedOperator (S : Source.SparseSystem) :
    EuclideanSpace ℝ (Fin S.n) →L[ℝ] EuclideanSpace ℝ (Fin S.n) :=
  Matrix.toEuclideanCLM (n := Fin S.n) (𝕜 := ℝ)
    ((normalizedMatrix S).map fun q => (q : ℝ))

theorem normalizedOperator_eq (S : Source.SparseSystem) :
    normalizedOperator S = ((matrixScale S : ℝ)⁻¹) • Source.operator S := by
  have hmat : ((normalizedMatrix S).map fun q => (q : ℝ)) =
      ((matrixScale S : ℝ)⁻¹) • Source.realMatrix S := by
    ext i j
    simp [normalizedMatrix, Source.realMatrix, div_eq_mul_inv, mul_comm]
  rw [normalizedOperator, hmat, map_smul]
  rfl

theorem normalizedOperator_norm_le_one (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : 0 < S.nnz) :
    ‖normalizedOperator S‖ ≤ 1 := by
  have hm0 : (0 : ℝ) < S.nnz := by exact_mod_cast hm
  have hn : (S.n : ℝ) ≤ S.nnz := by exact_mod_cast Source.dimension_le_nnz S hunit
  have hentry (i j : Fin S.n) : |(normalizedMatrix S i j : ℝ)| ≤ 1 / S.nnz := by
    have h : ((|normalizedMatrix S i j| : ℚ) : ℝ) ≤ ((1 / (S.nnz : ℚ) : ℚ) : ℝ) :=
      Rat.cast_le.mpr (normalizedMatrix_bound S hm i j)
    simpa only [Rat.cast_abs, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using h
  have hrow (i : Fin S.n) : ∑ j, |(normalizedMatrix S i j : ℝ)| ≤ 1 := by
    calc
      _ ≤ ∑ _j : Fin S.n, 1 / (S.nnz : ℝ) := Finset.sum_le_sum (fun j _ => hentry i j)
      _ = (S.n : ℝ) / S.nnz := by simp [div_eq_mul_inv]
      _ ≤ 1 := (div_le_one hm0).mpr hn
  have hcol (j : Fin S.n) : ∑ i, |(normalizedMatrix S i j : ℝ)| ≤ 1 := by
    calc
      _ ≤ ∑ _i : Fin S.n, 1 / (S.nnz : ℝ) := Finset.sum_le_sum (fun i _ => hentry i j)
      _ = (S.n : ℝ) / S.nnz := by simp [div_eq_mul_inv]
      _ ≤ 1 := (div_le_one hm0).mpr hn
  exact Maxwell.matrix_toEuclideanCLM_norm_le _ 1 (by norm_num) hrow hcol

theorem matrix_entry_le_operator_norm (S : Source.SparseSystem) (i j : Fin S.n) :
    |(S.matrix.toMatrix i j : ℝ)| ≤ ‖Source.operator S‖ := by
  let x : EuclideanSpace ℝ (Fin S.n) := WithLp.toLp 2 (Pi.single j 1)
  have hi := PiLp.norm_apply_le (Source.operator S x) i
  have hx : ‖x‖ = 1 := by simp [x]
  have he : Source.operator S x i = (S.matrix.toMatrix i j : ℝ) := by
    simp [Source.operator, Source.realMatrix, x,
      Matrix.mulVec, dotProduct]
  rw [he, Real.norm_eq_abs] at hi
  exact hi.trans (by simpa [hx] using (Source.operator S).le_opNorm x)

theorem matrixMax_le_operator_norm (S : Source.SparseSystem) :
    (matrixMax S : ℝ) ≤ ‖Source.operator S‖ := by
  by_cases hm : 0 < matrixMax S
  · obtain ⟨q, hq, he⟩ := magnitudeMax_attained (matrixValues S) hm
    obtain ⟨⟨i, j⟩, _, rfl⟩ := List.mem_map.mp hq
    have he' : |(S.matrix.toMatrix i j : ℝ)| = (matrixMax S : ℝ) := by exact_mod_cast he
    rw [← he']
    exact matrix_entry_le_operator_norm S i j
  · have hz : matrixMax S = 0 := le_antisymm (le_of_not_gt hm) (matrixMax_nonneg S)
    simp [hz]

theorem matrixScale_le_operator_norm (S : Source.SparseSystem) :
    (matrixScale S : ℝ) ≤ (S.nnz : ℝ) * ‖Source.operator S‖ := by
  simp only [matrixScale, Rat.cast_mul, Rat.cast_natCast]
  exact mul_le_mul_of_nonneg_left (matrixMax_le_operator_norm S) (Nat.cast_nonneg _)

noncomputable def normalizedUnit (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : 0 < S.nnz) :
    (EuclideanSpace ℝ (Fin S.n) →L[ℝ] EuclideanSpace ℝ (Fin S.n))ˣ where
  val := normalizedOperator S
  inv := (matrixScale S : ℝ) •
    Matrix.toEuclideanCLM (n := Fin S.n) (𝕜 := ℝ) (Source.realMatrix S)⁻¹
  val_inv := by
    have hs : (matrixScale S : ℝ) ≠ 0 := by
      exact_mod_cast (matrixScale_pos S hm).ne'
    have hi : Source.operator S * Matrix.toEuclideanCLM (n := Fin S.n) (𝕜 := ℝ)
        (Source.realMatrix S)⁻¹ = 1 := by
      rw [Source.operator, ← map_mul,
        Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hunit), map_one]
    apply ContinuousLinearMap.ext
    intro x
    simpa [normalizedOperator_eq, mul_apply_eq_comp, smul_smul, hs]
      using congrArg (fun T => T x) hi
  inv_val := by
    have hs : (matrixScale S : ℝ) ≠ 0 := by
      exact_mod_cast (matrixScale_pos S hm).ne'
    have hi : Matrix.toEuclideanCLM (n := Fin S.n) (𝕜 := ℝ)
        (Source.realMatrix S)⁻¹ * Source.operator S = 1 := by
      rw [Source.operator, ← map_mul,
        Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hunit), map_one]
    apply ContinuousLinearMap.ext
    intro x
    simpa [normalizedOperator_eq, mul_apply_eq_comp, smul_smul, hs]
      using congrArg (fun T => T x) hi

@[simp] theorem normalizedUnit_val (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : 0 < S.nnz) :
    (normalizedUnit S hunit hm : EuclideanSpace ℝ (Fin S.n) →L[ℝ] EuclideanSpace ℝ (Fin S.n)) =
      normalizedOperator S := rfl

theorem normalizedUnit_inverse_bound (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (hm : 0 < S.nnz) :
    ‖(↑((normalizedUnit S hunit hm)⁻¹) :
      EuclideanSpace ℝ (Fin S.n) →L[ℝ] EuclideanSpace ℝ (Fin S.n))‖ ≤
      (S.nnz : ℝ) * Maxwell.condition₂ (Source.realMatrix S) := by
  change ‖(matrixScale S : ℝ) •
    Matrix.toEuclideanCLM (n := Fin S.n) (𝕜 := ℝ) (Source.realMatrix S)⁻¹‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by exact_mod_cast matrixScale_pos S hm)]
  calc
    _ ≤ ((S.nnz : ℝ) * ‖Source.operator S‖) *
        ‖Matrix.toEuclideanCLM (n := Fin S.n) (𝕜 := ℝ) (Source.realMatrix S)⁻¹‖ :=
      mul_le_mul_of_nonneg_right (matrixScale_le_operator_norm S) (norm_nonneg _)
    _ = _ := by rw [Maxwell.condition₂, Source.operator]; ring

noncomputable def roundedOperator (S : Source.SparseSystem) (precision : ℕ) :
    EuclideanSpace ℝ (Fin S.n) →L[ℝ] EuclideanSpace ℝ (Fin S.n) :=
  Matrix.toEuclideanCLM (n := Fin S.n) (𝕜 := ℝ)
    ((Rounding.matrix precision (normalizedMatrix S)).map fun q => (q : ℝ))

theorem roundedOperator_error (S : Source.SparseSystem)
    (hunit : IsUnit (Source.realMatrix S)) (precision : ℕ) :
    ‖roundedOperator S precision - normalizedOperator S‖ ≤
      (S.nnz : ℝ) / (2 * 2 ^ precision) := by
  let E : Matrix (Fin S.n) (Fin S.n) ℝ := fun i j =>
    (Rounding.matrix precision (normalizedMatrix S) i j : ℝ) -
      (normalizedMatrix S i j : ℝ)
  have hentry (i j : Fin S.n) : |E i j| ≤ 1 / (2 * (2 : ℝ) ^ precision) := by
    dsimp [E]
    have h : ((|Rounding.matrix precision (normalizedMatrix S) i j - normalizedMatrix S i j| : ℚ) : ℝ) ≤
        ((1 / (2 * (2 : ℚ) ^ precision) : ℚ) : ℝ) :=
      Rat.cast_le.mpr (Rounding.matrix_entry_error precision (normalizedMatrix S) i j)
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
      Rat.cast_ofNat, Rat.cast_one] using h
  have hn : (S.n : ℝ) ≤ S.nnz := by exact_mod_cast Source.dimension_le_nnz S hunit
  have hrow (i : Fin S.n) : ∑ j, |E i j| ≤ (S.nnz : ℝ) / (2 * 2 ^ precision) := by
    calc
      _ ≤ ∑ _j : Fin S.n, 1 / (2 * (2 : ℝ) ^ precision) :=
        Finset.sum_le_sum (fun j _ => hentry i j)
      _ = (S.n : ℝ) / (2 * 2 ^ precision) := by simp [div_eq_mul_inv]
      _ ≤ _ := div_le_div_of_nonneg_right hn (by positivity)
  have hcol (j : Fin S.n) : ∑ i, |E i j| ≤ (S.nnz : ℝ) / (2 * 2 ^ precision) := by
    calc
      _ ≤ ∑ _i : Fin S.n, 1 / (2 * (2 : ℝ) ^ precision) :=
        Finset.sum_le_sum (fun i _ => hentry i j)
      _ = (S.n : ℝ) / (2 * 2 ^ precision) := by simp [div_eq_mul_inv]
      _ ≤ _ := div_le_div_of_nonneg_right hn (by positivity)
  have heq : roundedOperator S precision - normalizedOperator S =
      Matrix.toEuclideanCLM (n := Fin S.n) (𝕜 := ℝ) E := by
    rw [roundedOperator, normalizedOperator, ← map_sub]
    rfl
  rw [heq]
  exact Maxwell.matrix_toEuclideanCLM_norm_le E _ (by positivity) hrow hcol

end Maxwell.Logical.Normalization
