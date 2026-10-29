import Maxwell.Cost.DecoderTerm.Difference
import Maxwell.Cost.RationalAccumulator.Move

namespace Maxwell.Cost.DecoderTerm

abbrev magnitude (sample : List Bool) (center : ℕ) : ℕ :=
  addressValue (SignedDifference.magnitude sample center.bits)

def signed (sign : Bool) (n : ℕ) : ℚ := if sign then -(n : ℚ) else (n : ℚ)

theorem magnitude_bits_le (sample : List Bool) (center : ℕ) :
    (magnitude sample center).bits.length ≤ sample.length+center.bits.length+1 := by
  have h : (magnitude sample center).bits.length ≤
      (SignedDifference.magnitude sample center.bits).length := by
    rw [Nat.size_eq_bits_len, Nat.size_le]
    exact Subtraction.addressValue_lt_pow_length _
  exact h.trans ((SignedDifference.magnitude_length_le _ _).trans (by omega))

theorem signed_magnitude (sample : List Bool) (center : ℕ) :
    signed (SignedDifference.sign sample center.bits) (magnitude sample center) =
      (addressValue sample : ℚ)-center := by
  have h := SignedDifference.signed_value sample center.bits
  simp only [RationalAccumulator.address_bits] at h
  have hcast := congrArg (fun z : ℤ => (z : ℚ)) h
  cases hb : SignedDifference.sign sample center.bits <;>
    simpa [signed, magnitude, hb] using hcast

theorem signed_xor_mul (a b : Bool) (x y : ℕ) :
    signed (Bool.xor a b) (x*y) = signed a x * signed b y := by
  cases a <;> cases b <;> simp [signed]

theorem weighted_value (sample : List Bool) (center scale num den : ℕ) (negative : Bool) :
    signed (Bool.xor (SignedDifference.sign sample center.bits) negative)
      (magnitude sample center*num) / (scale*den : ℕ) =
      (signed negative num / den) * (((addressValue sample : ℚ)-center)/scale) := by
  rw [signed_xor_mul,signed_magnitude]
  simp only [Nat.cast_mul, div_eq_mul_inv,mul_inv_rev]
  ring

theorem signed_num (q : ℚ) : signed (decide (q.num < 0)) q.num.natAbs = (q.num : ℚ) := by
  by_cases h : q.num < 0
  · simp only [signed, h, decide_true, ↓reduceIte]
    have hn : (q.num.natAbs : ℤ) = -q.num := by rw [Int.natCast_natAbs,abs_of_neg h]
    have hc := congrArg (fun z : ℤ => (z : ℚ)) hn
    simp only [Int.cast_natCast,Int.cast_neg] at hc
    linarith
  · simp only [signed, h, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hn : (q.num.natAbs : ℤ) = q.num := by rw [Int.natCast_natAbs,abs_of_nonneg (by omega : 0 ≤ q.num)]
    have hc := congrArg (fun z : ℤ => (z : ℚ)) hn
    simpa only [Int.cast_natCast] using hc

theorem fixedPoint_value (F : Target.FixedPointFormat) (w : F.Word) (q : ℚ)
    (sample : List Bool) (hsample : addressValue sample = w.val) :
    signed (Bool.xor (SignedDifference.sign sample (2^(F.integerBits+F.fractionalBits)).bits)
      (decide (q.num < 0)))
      (magnitude sample (2^(F.integerBits+F.fractionalBits))*q.num.natAbs) /
      ((2^F.fractionalBits)*q.den : ℕ) = q * F.value w := by
  rw [weighted_value,signed_num,Rat.num_div_den,hsample]
  simp [Target.FixedPointFormat.value,Target.FixedPointFormat.numerator]

end Maxwell.Cost.DecoderTerm
