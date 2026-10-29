import Maxwell.Codec
import Mathlib.Data.Nat.Size

/-! Exact lengths of the concrete serializations. These count actual Boolean
lists and do not stand in for the separately required machine running time. -/

namespace Maxwell.Codec

theorem unsignedBitLength_eq_size (n : ℕ) : unsignedBitLength n = n.size := by
  by_cases hn : n = 0
  · simp [hn, unsignedBitLength]
  · simp only [unsignedBitLength, hn, ↓reduceIte]
    apply le_antisymm
    · exact Nat.succ_le_of_lt ((Nat.log2_lt hn).mpr (Nat.lt_size_self n))
    · exact Nat.size_le.mpr Nat.lt_log2_self

theorem unsignedBitLength_mono {m n : ℕ} (h : m ≤ n) :
    unsignedBitLength m ≤ unsignedBitLength n := by
  simpa only [unsignedBitLength_eq_size] using Nat.size_le_size h

theorem nat_length (n : ℕ) : (nat n).length = 2 * unsignedBitLength n + 1 := by
  simp [nat, Nat.size_eq_bits_len, unsignedBitLength_eq_size]
  omega

theorem int_length (z : ℤ) : (int z).length = 2 * signedBitLength z := by
  simp [int, nat_length, signedBitLength]
  omega

theorem rat_length (q : ℚ) :
    (rat q).length = 2 * (signedBitLength q.num + unsignedBitLength q.den) + 1 := by
  simp [rat, int_length, nat_length]
  omega

theorem rat_length_le {q : ℚ} {B : ℕ} (h : Source.ShortRational B q) :
    (rat q).length ≤ 4 * B + 1 := by
  have hn : signedBitLength q.num ≤ B := by exact_mod_cast h.1
  have hd : unsignedBitLength q.den ≤ B := by exact_mod_cast h.2
  rw [rat_length]
  omega

theorem flatMap_length_le {α : Type*} (encode : α → List Bool) (xs : List α)
    (B : ℕ) (h : ∀ x ∈ xs, (encode x).length ≤ B) :
    (xs.flatMap encode).length ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have hxs := ih (fun y hy => h y (by simp [hy]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    nlinarith

theorem list_length_le {α : Type*} (encode : α → List Bool) (xs : List α)
    (B : ℕ) (h : ∀ x ∈ xs, (encode x).length ≤ B) :
    (list encode xs).length ≤
      2 * unsignedBitLength xs.length + 1 + xs.length * B := by
  simpa only [list, List.length_append, nat_length] using
    Nat.add_le_add_left (flatMap_length_le encode xs B h)
      (2 * unsignedBitLength xs.length + 1)

/-- A nonsingular sparse input has an actual serialized length linear in its
stored nonzeros, coefficient bit budget, and logarithmic coordinate width.
There is no dense matrix scan or precomputed answer in this representation. -/
theorem source_length_le (S : Source.SparseSystem) (B : ℕ)
    (hunit : IsUnit (Source.realMatrix S))
    (hA : ∀ i j, Source.ShortRational B (S.matrix.toMatrix i j))
    (hb : ∀ i, Source.ShortRational B (S.source i)) :
    (source S).length ≤
      3 * (2 * unsignedBitLength S.nnz + 1) +
        S.nnz * (4 * unsignedBitLength S.nnz + 8 * B + 4) := by
  have hn := Source.dimension_le_nnz S hunit
  have hnb := unsignedBitLength_mono hn
  have hentry : ∀ p : {p // p ∈ sourceEntries S},
      (sourceEntry S p).length ≤ 4 * unsignedBitLength S.nnz + 4 * B + 3 := by
    intro p
    have hi := unsignedBitLength_mono (p.val.1.isLt.le.trans hn)
    have hj := unsignedBitLength_mono (p.val.2.isLt.le.trans hn)
    have hstored := (mem_sourceEntries S p.val).mp p.property
    have hc := rat_length_le (hA p.val.1 p.val.2)
    rw [SparseRationalMatrix.toMatrix_at_stored S.matrix p.val.1 p.val.2 hstored] at hc
    have hc' : (rat (S.matrix.coefficient
        ⟨p.val, (mem_sourceEntries S p.val).mp p.property⟩)).length ≤ 4 * B + 1 := hc
    simp only [sourceEntry, List.length_append, nat_length]
    omega
  have he := list_length_le (sourceEntry S) (sourceEntries S).attach
    (4 * unsignedBitLength S.nnz + 4 * B + 3) (fun p _ => hentry p)
  simp only [List.length_attach, sourceEntries_length] at he
  have hv := list_length_le rat (List.ofFn S.source) (4 * B + 1)
    (fun q hq => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hq
      exact rat_length_le (hb i))
  simp only [List.length_ofFn] at hv
  have hnv : S.n * (4 * B + 1) ≤ S.nnz * (4 * B + 1) :=
    Nat.mul_le_mul_right _ hn
  simp only [source, vector, List.length_append, nat_length]
  nlinarith

/-- Instantiation at the paper's actual logarithmic coefficient promise. -/
theorem promised_source_length_le (p : Source.Parameters) (S : Source.SparseSystem)
    (h : Source.Promises p S) :
    (source S).length ≤
      3 * (2 * unsignedBitLength S.nnz + 1) +
        S.nnz * (4 * unsignedBitLength S.nnz +
          8 * Nat.ceil (Source.bitBudget p S) + 4) := by
  apply source_length_le S _ h.1
  · intro i j
    have hh := h.2.2.1 i j
    exact ⟨hh.1.trans (Nat.le_ceil _), hh.2.trans (Nat.le_ceil _)⟩
  · intro i
    have hh := h.2.2.2 i
    exact ⟨hh.1.trans (Nat.le_ceil _), hh.2.trans (Nat.le_ceil _)⟩

end Maxwell.Codec
