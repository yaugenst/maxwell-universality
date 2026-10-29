import Maxwell.Cost.MagnitudeMax.Both
import Maxwell.Codec.Bounds

namespace Maxwell.Cost.MagnitudeMax.Both

/-- One pass over all sparse entries and RHS scalars, with both arithmetic
maxima, count preservation, pair archival, and the zero flag fully charged. -/
theorem recordPrice_le (R : Codec.SourceRecord) (B : ℕ) :
    recordPrice R B ≤ 13000 * ((ParseSource.recordWire R).length + 1) *
      ((B + 2)^2 + R.dimension.bits.length + R.entries.length.bits.length + R.rhs.length.bits.length + 1) := by
  have hl := ParseSource.recordWire_length R
  have hlenE := LogEntries.records_length R.entries
  have hlenR := LogRats.records_length R.rhs
  let N := (ParseSource.recordWire R).length + 1
  let K := R.dimension.bits.length + R.entries.length.bits.length + R.rhs.length.bits.length + 1
  have hn : R.entries.length + 1 ≤ N := by dsimp [N]; omega
  have hm : R.rhs.length + 1 ≤ N := by dsimp [N]; omega
  have hsum : R.entries.length + R.rhs.length ≤ N := by dsimp [N]; omega
  have hkE : 13 * R.entries.length.bits.length + 15 ≤ 15 * K := by dsimp [K]; omega
  have hkR : 13 * R.rhs.length.bits.length + 15 ≤ 15 * K := by dsimp [K]; omega
  have heCounter : (R.entries.length + 1) * (13 * R.entries.length.bits.length + 15) ≤ 15 * N * K := by
    calc
      _ ≤ N * (15 * K) := Nat.mul_le_mul hn hkE
      _ = _ := by ring
  have hrCounter : (R.rhs.length + 1) * (13 * R.rhs.length.bits.length + 15) ≤ 15 * N * K := by
    calc
      _ ≤ N * (15 * K) := Nat.mul_le_mul hm hkR
      _ = _ := by ring
  have hmaximum : R.entries.length * (12000 * (B + 2)^2) +
      R.rhs.length * (11000 * (B + 2)^2) ≤ 12000 * N * (B + 2)^2 := by
    have h := Nat.mul_le_mul_right (12000 * (B + 2)^2) hsum
    nlinarith
  have hlinear : 21 * R.dimension.bits.length + 36 * R.entries.length.bits.length +
      21 * R.rhs.length.bits.length + 157 ≤ 157 * N := by dsimp [N]; omega
  have hk : 1 ≤ K := by dsimp [K]; omega
  have hbase : N ≤ N * K := by nlinarith
  have hn1 : 1 ≤ N := by dsimp [N]; omega
  have hB : B ≤ (B + 2)^2 := by nlinarith
  have hb : 72 * B ≤ 72 * N * (B + 2)^2 := by
    have h := Nat.mul_le_mul hn1 hB
    nlinarith
  change recordPrice R B ≤ 13000 * N * ((B + 2)^2 +
    R.dimension.bits.length + R.entries.length.bits.length + R.rhs.length.bits.length + 1)
  have hK : (B + 2)^2 + R.dimension.bits.length + R.entries.length.bits.length + R.rhs.length.bits.length + 1 =
      (B + 2)^2 + K := by dsimp [K]; ring
  rw [hK]
  dsimp only [recordPrice, Front.price, Entries.price, SourceLoop.price, Tail.price, Parse.price, Loop.price]
  nlinarith

theorem price_le (S : Source.SparseSystem) (B : ℕ) :
    price S B ≤ 13000 * ((Codec.source S).length + 1) *
      ((B + 2)^2 + 2 * S.n.bits.length + S.nnz.bits.length + 1) := by
  have h := recordPrice_le (Codec.sourceRecord S) B
  rw [ParseSource.source_wire] at h
  simpa [price, Codec.sourceRecord, Codec.sourceEntries_length,
    two_mul, add_assoc, add_left_comm, add_comm] using h

theorem promised_price_le (p : Source.Parameters) (S : Source.SparseSystem)
    (h : Source.Promises p S) :
    price S (inputWidth p S) ≤
      13000 * (3 * (2 * unsignedBitLength S.nnz + 1) +
        S.nnz * (4 * unsignedBitLength S.nnz + 8 * Nat.ceil (Source.bitBudget p S) + 4) + 1) *
        ((inputWidth p S + 2)^2 + 3 * unsignedBitLength S.nnz + 1) := by
  apply (price_le S (inputWidth p S)).trans
  apply Nat.mul_le_mul
  · exact Nat.mul_le_mul_left 13000 (Nat.add_le_add_right (Codec.promised_source_length_le p S h) 1)
  · have hn := Codec.unsignedBitLength_mono (Source.dimension_le_nnz S h.1)
    simp only [Codec.unsignedBitLength_eq_size, Nat.size_eq_bits_len] at hn ⊢
    omega

end Maxwell.Cost.MagnitudeMax.Both
