import Maxwell.Continuum.RoundedIntegerRegister
import Maxwell.Continuum.DyadicMagnitudeBits
import Maxwell.Continuum.RationalFiniteWidths

/-! Canonical rounded output widths depend on the represented magnitude,
not on the possibly large unreduced denominator of the input register. -/
namespace Maxwell.Continuum.RationalDataflow.RoundedInteger
open Maxwell.Cost

theorem rounded_abs (P A : ℕ) (q : ℚ) (hq : |q|≤(2:ℚ)^A) :
    |(roundDyadic P q).value|≤(2:ℚ)^(A+1) := by
  have he := roundDyadic_error_rat P q
  have hhalf : (1/2:ℚ)^P≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hpow : (1:ℚ)≤(2:ℚ)^A := one_le_pow₀ (by norm_num)
  have ht := abs_add_le ((roundDyadic P q).value-q) q
  rw [sub_add_cancel] at ht
  rw [abs_sub_comm] at he
  rw [pow_succ]
  linarith only [he,hhalf,hpow,ht,hq]

theorem result_magnitude_width (P A : ℕ) (x : Parts) (hx : |x.value|≤(2:ℚ)^A) :
    (result P x).Width (P+A+4) := by
  have hn := dyadic_numerator_bits_of_bound (roundDyadic P x.value) (rounded_abs P A x.value hx)
  unfold Dyadic.numeratorBits signedBitLength at hn
  rw [Codec.unsignedBitLength_eq_size,←Nat.size_eq_bits_len] at hn
  have hw := Parts.literal_width (RationalWords.width_int (roundDyadic P x.value).numerator)
  exact hw.mono (by omega)

#print axioms result_magnitude_width
end Maxwell.Continuum.RationalDataflow.RoundedInteger
