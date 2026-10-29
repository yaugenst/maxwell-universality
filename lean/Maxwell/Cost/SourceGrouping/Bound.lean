import Maxwell.Cost.SourceGrouping
import Maxwell.Codec.Bounds

namespace Maxwell.Cost.SourceGrouping

/-- The complete real machine cost on the paper's input promise. The only
size factors are stored nonzeros, binary coordinate width, and the promised
coefficient width; no dimension-squared traversal is charged or performed. -/
theorem promised_price_le (p : Source.Parameters) (S : Source.SparseSystem)
    (h : Source.Promises p S) :
    price S ≤
      100 * (3 * (2 * unsignedBitLength S.nnz + 1) +
        S.nnz * (4 * unsignedBitLength S.nnz + 8 * Nat.ceil (Source.bitBudget p S) + 4) + 1) *
        (3 * unsignedBitLength S.nnz + 1) := by
  apply (price_le S).trans
  apply Nat.mul_le_mul
  · exact Nat.mul_le_mul_left 100 (Nat.add_le_add_right (Codec.promised_source_length_le p S h) 1)
  · have hn := Codec.unsignedBitLength_mono (Source.dimension_le_nnz S h.1)
    simp only [Codec.unsignedBitLength_eq_size, Nat.size_eq_bits_len] at hn ⊢
    omega

end Maxwell.Cost.SourceGrouping
