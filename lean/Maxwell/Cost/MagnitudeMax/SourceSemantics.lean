import Maxwell.Cost.MagnitudeMax.SourceLoop
import Maxwell.Logical.CachedNormalization
import Maxwell.Codec.Bounds

namespace Maxwell.Cost.MagnitudeMax

open Logical.Normalization

theorem source_values (S : Source.SparseSystem) :
    SourceLoop.values (Codec.sourceRecord S).entries = matrixValues S := by
  rw [SourceLoop.values, Logical.CachedNormalization.sourceRecord_eq,
    Logical.CachedNormalization.stored_eq]
  simp [matrixValues, List.map_map, Function.comp_def]

theorem source_maximum_value (S : Source.SparseSystem) :
    value (maximum (SourceLoop.values (Codec.sourceRecord S).entries)) = matrixMax S := by
  rw [maximum_value, source_values]
  rfl

theorem source_matrixScale (S : Source.SparseSystem) :
    (S.nnz : ℚ) * value (maximum (SourceLoop.values (Codec.sourceRecord S).entries)) = matrixScale S := by
  rw [source_maximum_value]
  rfl

theorem scan_pos (current : Pair) (qs : List ℚ) (h : 0 < current.2) : 0 < (scan current qs).2 := by
  induction qs generalizing current with
  | nil => exact h
  | cons q qs ih => exact ih (select current q) (select_pos current q h)

theorem maximum_pos (qs : List ℚ) : 0 < (maximum qs).2 := scan_pos (0, 1) qs (by decide)

theorem maximum_num_zero_iff (qs : List ℚ) : (maximum qs).1 = 0 ↔ ∀ q ∈ qs, q = 0 := by
  constructor
  · intro h q hq
    have hm : magnitudeMax qs = 0 := by
      rw [← maximum_value]
      simp [value, h]
    have ha := abs_le_magnitudeMax hq
    rw [hm] at ha
    exact abs_eq_zero.mp (le_antisymm ha (abs_nonneg q))
  · intro h
    rcases maximum_selected qs with hm | ⟨q, hq, hm⟩
    · simp [hm]
    · simp [hm, h q hq]

theorem rhs_maximum_value (S : Source.SparseSystem) :
    value (maximum (List.ofFn S.source)) = sourceScale S := maximum_value _

theorem rhs_maximum_zero_iff (S : Source.SparseSystem) :
    (maximum (List.ofFn S.source)).1 = 0 ↔ S.source = 0 := by
  rw [maximum_num_zero_iff]
  constructor
  · intro h
    funext i
    exact h (S.source i) (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · intro h q hq
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
    simp [h]

noncomputable def inputWidth (p : Source.Parameters) (S : Source.SparseSystem) : ℕ :=
  unsignedBitLength S.nnz + Nat.ceil (Source.bitBudget p S) + 1

theorem inputWidth_pos (p : Source.Parameters) (S : Source.SparseSystem) : 1 ≤ inputWidth p S := by
  unfold inputWidth
  omega

private theorem promised_rat_width (p : Source.Parameters) (S : Source.SparseSystem) (q : ℚ)
    (h : Source.ShortRational (Source.bitBudget p S) q) :
    q.num.natAbs.bits.length ≤ inputWidth p S ∧ q.den.bits.length ≤ inputWidth p S := by
  have hn : signedBitLength q.num ≤ Nat.ceil (Source.bitBudget p S) := by
    exact_mod_cast h.1.trans (Nat.le_ceil _)
  have hd : unsignedBitLength q.den ≤ Nat.ceil (Source.bitBudget p S) := by
    exact_mod_cast h.2.trans (Nat.le_ceil _)
  simp only [signedBitLength, Codec.unsignedBitLength_eq_size] at hn hd
  simp only [inputWidth, Nat.size_eq_bits_len]
  omega

theorem promised_entry_width (p : Source.Parameters) (S : Source.SparseSystem) (h : Source.Promises p S) :
    ∀ entry ∈ (Codec.sourceRecord S).entries, SourceLoop.Width (inputWidth p S) entry := by
  intro entry he
  rw [Logical.CachedNormalization.sourceRecord_eq, Logical.CachedNormalization.stored_eq,
    List.map_map] at he
  obtain ⟨ij, _, rfl⟩ := List.mem_map.mp he
  have hn := Source.dimension_le_nnz S h.1
  have hi := Codec.unsignedBitLength_mono (ij.1.isLt.le.trans hn)
  have hj := Codec.unsignedBitLength_mono (ij.2.isLt.le.trans hn)
  simp only [Codec.unsignedBitLength_eq_size] at hi hj
  refine ⟨?_, ?_, promised_rat_width p S _ (h.2.2.1 ij.1 ij.2)⟩ <;>
    dsimp [inputWidth] <;> simp only [Codec.unsignedBitLength_eq_size, Nat.size_eq_bits_len] <;> omega

theorem promised_rhs_width (p : Source.Parameters) (S : Source.SparseSystem) (h : Source.Promises p S) :
    ∀ q ∈ List.ofFn S.source, q.num.natAbs.bits.length ≤ inputWidth p S ∧ q.den.bits.length ≤ inputWidth p S := by
  intro q hq
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
  exact promised_rat_width p S _ (h.2.2.2 i)

end Maxwell.Cost.MagnitudeMax
