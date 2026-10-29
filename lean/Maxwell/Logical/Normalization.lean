import Maxwell.Source
import Maxwell.Codec
import Maxwell.Logical.DyadicCompile
import Maxwell.Logical.Rounding

/-! Rational source normalization and actual signed dyadic gate inputs. -/

namespace Maxwell.Logical.Normalization

def magnitudeMax : List ℚ → ℚ
  | [] => 0
  | q :: qs => max |q| (magnitudeMax qs)

theorem magnitudeMax_nonneg (qs : List ℚ) : 0 ≤ magnitudeMax qs := by
  induction qs with
  | nil => exact le_rfl
  | cons q qs ih => exact ih.trans (le_max_right _ _)

theorem abs_le_magnitudeMax {q : ℚ} {qs : List ℚ} (h : q ∈ qs) :
    |q| ≤ magnitudeMax qs := by
  induction qs with
  | nil => simp at h
  | cons r rs ih =>
      rcases List.mem_cons.mp h with rfl | h
      · exact le_max_left _ _
      · exact (ih h).trans (le_max_right _ _)

def matrixValues (S : Source.SparseSystem) : List ℚ :=
  (Codec.sourceEntries S).map fun p => S.matrix.toMatrix p.1 p.2

def matrixMax (S : Source.SparseSystem) : ℚ := magnitudeMax (matrixValues S)
def matrixScale (S : Source.SparseSystem) : ℚ := S.nnz * matrixMax S
def sourceScale (S : Source.SparseSystem) : ℚ := magnitudeMax (List.ofFn S.source)
def normalizedMatrix (S : Source.SparseSystem) : Matrix (Fin S.n) (Fin S.n) ℚ :=
  fun i j => S.matrix.toMatrix i j / matrixScale S
def normalizedSource (S : Source.SparseSystem) : Fin S.n → ℚ :=
  fun i => S.source i / sourceScale S

theorem matrixMax_nonneg (S : Source.SparseSystem) : 0 ≤ matrixMax S :=
  magnitudeMax_nonneg _

theorem matrix_entry_le (S : Source.SparseSystem) (i j : Fin S.n) :
    |S.matrix.toMatrix i j| ≤ matrixMax S := by
  by_cases h : (i, j) ∈ S.matrix.support
  · apply abs_le_magnitudeMax
    exact List.mem_map.mpr ⟨(i, j), (Codec.mem_sourceEntries S (i, j)).mpr h, rfl⟩
  · have hz : S.matrix.toMatrix i j = 0 := by
      simp [SparseRationalMatrix.toMatrix, h]
    simpa [hz] using matrixMax_nonneg S

theorem matrixMax_pos (S : Source.SparseSystem) (hm : 0 < S.nnz) :
    0 < matrixMax S := by
  obtain ⟨⟨i, j⟩, hij⟩ := Finset.card_pos.mp hm
  have hn := (SparseRationalMatrix.toMatrix_ne_zero_iff S.matrix i j).mpr hij
  exact (abs_pos.mpr hn).trans_le (matrix_entry_le S i j)

theorem matrixScale_pos (S : Source.SparseSystem) (hm : 0 < S.nnz) :
    0 < matrixScale S := mul_pos (by exact_mod_cast hm) (matrixMax_pos S hm)

theorem normalizedMatrix_zero (S : Source.SparseSystem) (i j : Fin S.n)
    (h : S.matrix.toMatrix i j = 0) : normalizedMatrix S i j = 0 := by
  simp [normalizedMatrix, h]

theorem normalizedMatrix_bound (S : Source.SparseSystem) (hm : 0 < S.nnz)
    (i j : Fin S.n) : |normalizedMatrix S i j| ≤ 1 / (S.nnz : ℚ) := by
  have hm0 : (0 : ℚ) < S.nnz := by exact_mod_cast hm
  have hmax := matrixMax_pos S hm
  rw [normalizedMatrix, abs_div, abs_of_pos (matrixScale_pos S hm)]
  calc
    _ ≤ matrixMax S / matrixScale S :=
      div_le_div_of_nonneg_right (matrix_entry_le S i j) (matrixScale_pos S hm).le
    _ = 1 / (S.nnz : ℚ) := by
      unfold matrixScale
      field_simp

theorem normalizedMatrix_half_bound (S : Source.SparseSystem) (hm : 2 ≤ S.nnz)
    (i j : Fin S.n) : |normalizedMatrix S i j| ≤ 1 / 2 := by
  apply (normalizedMatrix_bound S (by omega) i j).trans
  exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hm)

theorem source_entry_le (S : Source.SparseSystem) (i : Fin S.n) :
    |S.source i| ≤ sourceScale S :=
  abs_le_magnitudeMax (List.mem_ofFn.mpr ⟨i, rfl⟩)

theorem sourceScale_pos (S : Source.SparseSystem) (hb : S.source ≠ 0) :
    0 < sourceScale S := by
  obtain ⟨i, hi⟩ : ∃ i, S.source i ≠ 0 := by
    by_contra! h
    exact hb (funext h)
  exact (abs_pos.mpr hi).trans_le (source_entry_le S i)

theorem normalizedSource_bound (S : Source.SparseSystem) (hb : S.source ≠ 0)
    (i : Fin S.n) : |normalizedSource S i| ≤ 1 := by
  rw [normalizedSource, abs_div, abs_of_pos (sourceScale_pos S hb),
    div_le_one (sourceScale_pos S hb)]
  exact source_entry_le S i

theorem nearest_abs_lt_one (precision : ℕ) (hs : 1 ≤ precision)
    (q : ℚ) (hq : |q| ≤ 1 / 2) : |(Rounding.nearest precision q).value| < 1 := by
  have hp : (2 : ℚ) ≤ 2 ^ precision := by
    simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) hs)
  have he := Rounding.nearest_error precision q
  have he' : |(Rounding.nearest precision q).value - q| ≤ 1 / 4 := by
    apply he.trans
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  have htri := abs_add_le ((Rounding.nearest precision q).value - q) q
  rw [sub_add_cancel] at htri
  linarith

theorem nearest_numerator_lt (precision : ℕ) (hs : 1 ≤ precision)
    (q : ℚ) (hq : |q| ≤ 1 / 2) :
    (Rounding.nearest precision q).numerator.natAbs < 2 ^ precision := by
  have h := nearest_abs_lt_one precision hs q hq
  rw [Dyadic.value, abs_div, abs_of_pos (by positivity : (0 : ℚ) < 2 ^ precision),
    div_lt_one (by positivity)] at h
  have hi : |(Rounding.nearest precision q).numerator| < (2 ^ precision : ℤ) := by
    exact_mod_cast h
  rw [← Int.natCast_natAbs] at hi
  exact_mod_cast hi

def dyadicTerm {n : ℕ} (precision : ℕ) (q : ℚ) (j : Fin n) : DyadicTerm n where
  bits := Horner.encode precision (Rounding.nearest precision q).numerator.natAbs
  negative := decide ((Rounding.nearest precision q).numerator < 0)
  input := j

@[simp] theorem dyadicTerm_length {n : ℕ} (precision : ℕ) (q : ℚ) (j : Fin n) :
    (dyadicTerm precision q j).bits.length = precision := Horner.encode_length _ _

theorem dyadicTerm_coefficient {n : ℕ} (precision : ℕ) (hs : 1 ≤ precision)
    (q : ℚ) (hq : |q| ≤ 1 / 2) (j : Fin n) :
    (dyadicTerm precision q j).coefficient = (Rounding.nearest precision q).value := by
  rw [DyadicTerm.coefficient]
  simp only [dyadicTerm, decide_eq_true_eq]
  rw [Horner.coefficient_encode precision _ (nearest_numerator_lt precision hs q hq)]
  unfold Dyadic.value
  split_ifs with hn
  · rw [← neg_div]
    congr 1
    have h : -((Rounding.nearest precision q).numerator.natAbs : ℤ) =
        (Rounding.nearest precision q).numerator := by
          rw [Int.ofNat_natAbs_of_nonpos hn.le, neg_neg]
    exact_mod_cast h
  · congr 1
    exact congrArg (fun z : ℤ => (z : ℚ)) (Int.natAbs_of_nonneg (le_of_not_gt hn))

end Maxwell.Logical.Normalization
