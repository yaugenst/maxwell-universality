import Maxwell.Cost.NormalizeCoefficient.PadReverse.Tapes
import Maxwell.Logical.Horner
import Mathlib.Data.Nat.Size

namespace Maxwell.Cost.NormalizeCoefficient.PadReverse

private theorem numerator_append (xs ys : List Bool) :
    Logical.Horner.numerator (xs++ys) =
      Logical.Horner.numerator xs * 2^ys.length + Logical.Horner.numerator ys := by
  induction xs with
  | nil => simp [Logical.Horner.numerator]
  | cons b xs ih =>
    cases b <;> simp only [List.cons_append, Logical.Horner.numerator,
      Bool.false_eq_true, ↓reduceIte, List.length_append, pow_add, ih] <;> ring

private theorem numerator_reverse (bits : List Bool) :
    Logical.Horner.numerator bits.reverse = addressValue bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    rw [List.reverse_cons, numerator_append, ih]
    cases b <;> simp [Logical.Horner.numerator, addressValue] <;> omega

private theorem encode_numerator (bits : List Bool) :
    Logical.Horner.encode bits.length (Logical.Horner.numerator bits) = bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    have ht := Logical.Horner.numerator_lt_denominator bits
    cases b with
    | false =>
      simpa [Logical.Horner.encode, Logical.Horner.numerator,
        Nat.not_le.mpr ht, Nat.mod_eq_of_lt ht] using congrArg (List.cons false) ih
    | true =>
      simp only [List.length_cons, Logical.Horner.numerator, ↓reduceIte, Logical.Horner.encode]
      have hd : 2^bits.length ≤ 2^bits.length+Logical.Horner.numerator bits := by omega
      simp only [hd, decide_true]
      simp only [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt ht, ih]

private theorem addressValue_false_padding (bits : List Bool) (extra : ℕ) :
    addressValue (bits ++ List.replicate extra false) = addressValue bits := by
  induction bits with
  | nil =>
    induction extra with
    | zero => rfl
    | succ extra ih =>
      change addressValue (List.replicate extra false) = 0 at ih
      simp [List.replicate_succ, addressValue, ih]
  | cons b bits ih => simp [addressValue, ih]

theorem bits_length_le (n precision : ℕ) (hn : n < 2^precision) :
    n.bits.length ≤ precision := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr hn

/-- The actual pad-and-reverse tape routine produces precisely the
most-significant-first word consumed by the logical Horner compiler. -/
theorem padded_reverse_eq_encode (n precision : ℕ) (hn : n < 2^precision) :
    (padded precision n.bits).reverse = Logical.Horner.encode precision n := by
  have hl := bits_length_le n precision hn
  have hlen : (padded precision n.bits).reverse.length = precision := by
    simp [padded]
    omega
  have hnumer : Logical.Horner.numerator (padded precision n.bits).reverse = n := by
    rw [numerator_reverse, padded, addressValue_false_padding, addressValue_bits]
  have he := encode_numerator (padded precision n.bits).reverse
  rw [hlen, hnumer] at he
  exact he.symm

end Maxwell.Cost.NormalizeCoefficient.PadReverse
