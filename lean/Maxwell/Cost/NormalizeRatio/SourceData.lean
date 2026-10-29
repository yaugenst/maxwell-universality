import Maxwell.Cost.NormalizeRatio
import Maxwell.Cost.MagnitudeMax.Semantics

/-! Binding the machine's unreduced scale pair to the manuscript's actual
normalization. The maximum pair is selected from the parsed source stream. -/
namespace Maxwell.Cost.NormalizeRatio
open Structured RationalAccumulator
open Logical.Normalization

/-- Data values for the fixed normalization bank, before the finite routine
loads its temporary words. This is a semantic description, not machine code. -/
def coefficientBank (q : ℚ) (scale : ℕ × ℕ) (precision : ℕ) : ℕ → ℕ
  | 30 => q.num.natAbs
  | 31 => q.den
  | 32 => scale.1
  | 33 => scale.2
  | 34 => 2^precision
  | _ => 0

theorem signed_natAbs (q : ℚ) :
    (if decide (q.num < 0) then -(q.num.natAbs:ℚ) else q.num.natAbs) = q.num := by
  by_cases h : q.num < 0
  · simp only [h, decide_true, ↓reduceIte]
    have he : -(q.num.natAbs:ℤ) = q.num := by
      rw [Int.ofNat_natAbs_of_nonpos h.le, neg_neg]
    exact_mod_cast he
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact congrArg (fun z : ℤ => (z : ℚ)) (Int.natAbs_of_nonneg (le_of_not_gt h))

theorem coefficientBank_normalized (q : ℚ) (scale : ℕ × ℕ) (precision : ℕ) :
    normalized (coefficientBank q scale precision) (decide (q.num < 0)) =
      q / ((scale.1:ℚ)/scale.2) := by
  unfold normalized
  change ((if decide (q.num < 0) then -(q.num.natAbs:ℚ) else q.num.natAbs) / q.den) / ((scale.1:ℚ)/scale.2) = _
  rw [signed_natAbs, q.num_div_den]

theorem maximum_denominator_pos (qs : List ℚ) :
    0 < (MagnitudeMax.maximum qs).2 := by
  rcases MagnitudeMax.maximum_selected qs with h | ⟨q, _, h⟩
  · simp [h]
  · simpa [h] using q.den_pos

theorem maximum_numerator_pos (qs : List ℚ) (h : 0 < magnitudeMax qs) :
    0 < (MagnitudeMax.maximum qs).1 := by
  have he := MagnitudeMax.maximum_value qs
  unfold MagnitudeMax.value at he
  by_contra! hz
  have hz' : (MagnitudeMax.maximum qs).1 = 0 := by omega
  rw [hz'] at he
  simp only [Nat.cast_zero, zero_div] at he
  linarith

/-- Multiply the selected maximum numerator by the actual nonzero count;
the denominator stays unchanged. No gcd or fraction reduction is required. -/
def matrixScalePair (S : Source.SparseSystem) : ℕ × ℕ :=
  let selected := MagnitudeMax.maximum (matrixValues S)
  (S.nnz*selected.1, selected.2)

theorem matrixScalePair_value (S : Source.SparseSystem) :
    ((matrixScalePair S).1:ℚ)/(matrixScalePair S).2 = matrixScale S := by
  have hm := MagnitudeMax.maximum_value (matrixValues S)
  change _ = matrixMax S at hm
  unfold MagnitudeMax.value at hm
  simp only [matrixScalePair, matrixScale, Nat.cast_mul]
  rw [mul_div_assoc, hm]

theorem matrixScalePair_positive (S : Source.SparseSystem) (hm : 0 < S.nnz) :
    0 < (matrixScalePair S).1 ∧ 0 < (matrixScalePair S).2 := by
  exact ⟨Nat.mul_pos hm (maximum_numerator_pos _ (matrixMax_pos S hm)),
    maximum_denominator_pos _⟩

theorem matrix_coefficient_normalized (S : Source.SparseSystem) (precision : ℕ)
    (i j : Fin S.n) :
    normalized (coefficientBank (S.matrix.toMatrix i j) (matrixScalePair S) precision)
      (decide ((S.matrix.toMatrix i j).num < 0)) = normalizedMatrix S i j := by
  rw [coefficientBank_normalized, matrixScalePair_value]
  rfl

/-- The actual finite normalizer returns the same rounded matrix coefficient
used by the logical compiler, including coefficients rounded to zero. -/
theorem matrix_normalizes (S : Source.SparseSystem) (precision B : ℕ)
    (i j : Fin S.n) (hm : 2 ≤ S.nnz) (hs : 1 ≤ precision)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hbits : ∀ k, 30 ≤ k → k ≤ 34 →
      (coefficientBank (S.matrix.toMatrix i j) (matrixScalePair S) precision k).bits.length ≤ B)
    (hbank : Bank s.val (coefficientBank (S.matrix.toMatrix i j) (matrixScalePair S) precision))
    (hready : Scratch s.val 0) (hfour : Blank s.val 4)
    (hsign : s.val.registers 35 = decide ((S.matrix.toMatrix i j).num < 0)) :
    ∃ cost, ∃ t : Store, cost ≤ 100000*(B+2)^2 ∧
      Executes input tape code cost s t ∧
      SignedRound.Output t.val (Logical.Rounding.nearest precision (normalizedMatrix S i j)).numerator ∧
      (Logical.Rounding.nearest precision (normalizedMatrix S i j)).numerator.natAbs < 2^precision ∧
      Bank t.val (coefficientBank (S.matrix.toMatrix i j) (matrixScalePair S) precision) ∧
      Scratch t.val 0 ∧ Frame s.val t.val := by
  have hscale := matrixScalePair_positive S (by omega)
  obtain ⟨cost, t, hc, he, ho, hb, hr, hf⟩ := normalizes input tape
    (coefficientBank (S.matrix.toMatrix i j) (matrixScalePair S) precision) B precision
    (decide ((S.matrix.toMatrix i j).num < 0)) hbits
    (S.matrix.toMatrix i j).den_pos hscale.1 hscale.2 rfl rfl rfl
    s hbank hready hfour hsign
  rw [matrix_coefficient_normalized] at ho
  exact ⟨cost, t, hc, he, ho,
    nearest_numerator_lt precision hs _ (normalizedMatrix_half_bound S hm i j), hb, hr, hf⟩

theorem matrixScalePair_bits (S : Source.SparseSystem) (B : ℕ)
    (hB : 1 ≤ B)
    (hnum : ∀ q ∈ matrixValues S, q.num.natAbs.bits.length ≤ B)
    (hden : ∀ q ∈ matrixValues S, q.den.bits.length ≤ B) :
    (matrixScalePair S).1.bits.length ≤ S.nnz.bits.length+B ∧
    (matrixScalePair S).2.bits.length ≤ B := by
  have hh := MagnitudeMax.maximum_width (matrixValues S) B B hB hnum hden
  exact ⟨(bits_mul_le _ _).trans (Nat.add_le_add_left hh.1 _), hh.2⟩

/-- Positive right-hand-side normalization uses the same selected raw pair. -/
def sourceScalePair (S : Source.SparseSystem) : ℕ × ℕ :=
  MagnitudeMax.maximum (List.ofFn S.source)

theorem sourceScalePair_value (S : Source.SparseSystem) :
    ((sourceScalePair S).1:ℚ)/(sourceScalePair S).2 = sourceScale S :=
  MagnitudeMax.maximum_value _

theorem sourceScalePair_positive (S : Source.SparseSystem) (hb : S.source ≠ 0) :
    0 < (sourceScalePair S).1 ∧ 0 < (sourceScalePair S).2 :=
  ⟨maximum_numerator_pos _ (sourceScale_pos S hb), maximum_denominator_pos _⟩

theorem source_coefficient_normalized (S : Source.SparseSystem) (precision : ℕ)
    (i : Fin S.n) :
    normalized (coefficientBank (S.source i) (sourceScalePair S) precision)
      (decide ((S.source i).num < 0)) = normalizedSource S i := by
  rw [coefficientBank_normalized, sourceScalePair_value]
  rfl

end Maxwell.Cost.NormalizeRatio
