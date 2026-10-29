import Maxwell.Cost.TapeOps

namespace Maxwell.Cost.TapeOps

theorem addressValue_append_true_pos (bits : List Bool) :
    0 < addressValue (bits ++ [true]) := by
  induction bits with
  | nil => simp [addressValue]
  | cons b bits ih =>
    simp only [List.cons_append, addressValue]
    omega

/-- Removing high zero bits gives exactly the canonical binary string used
by the concrete input/output codec, not merely a value-equivalent string. -/
theorem canonicalBits_bits {bits : List Bool} (h : CanonicalBits bits) :
    (addressValue bits).bits = bits := by
  rcases h with rfl | ⟨preceding, rfl⟩
  · rfl
  · induction preceding with
    | nil => simp [addressValue]
    | cons b preceding ih =>
      have hpos := addressValue_append_true_pos preceding
      cases b <;> simp only [List.cons_append, addressValue, Bool.toNat_false,
        Bool.toNat_true, zero_add]
      · rw [Nat.bit0_bits _ (by omega), ih]
      · rw [show 1 + 2 * addressValue (preceding ++ [true]) =
          2 * addressValue (preceding ++ [true]) + 1 by omega, Nat.bit1_bits, ih]

theorem canonicalBits_eq_of_value_eq {xs ys : List Bool}
    (hx : CanonicalBits xs) (hy : CanonicalBits ys)
    (hvalue : addressValue xs = addressValue ys) : xs = ys := by
  rw [← canonicalBits_bits hx, ← canonicalBits_bits hy, hvalue]

end Maxwell.Cost.TapeOps
