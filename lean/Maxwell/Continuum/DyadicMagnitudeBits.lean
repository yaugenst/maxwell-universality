import Maxwell.Continuum.ComplexDyadic
import Maxwell.Codec.Bounds

/-! Exact stored-word lengths from fixed-point magnitude bounds. -/

namespace Maxwell.Continuum

theorem dyadic_numerator_bits_of_bound {P B : ℕ} (d : Dyadic P)
    (hd : |d.value|≤(2:ℚ)^B) : d.numeratorBits≤P+B+2 := by
  rw [Dyadic.value,abs_div,abs_pow,abs_of_nonneg (by norm_num : (0:ℚ)≤2)] at hd
  have h := (div_le_iff₀ (by positivity : (0:ℚ)<2^P)).mp hd
  rw [← pow_add,← Int.cast_abs] at h
  have hi : |d.numerator|≤(2:ℤ)^(B+P) := by exact_mod_cast h
  rw [← Int.natCast_natAbs] at hi
  have hn : d.numerator.natAbs≤2^(B+P) := by exact_mod_cast hi
  have hb := Codec.unsignedBitLength_mono hn
  rw [Dyadic.denominator_bitLength] at hb
  unfold Dyadic.numeratorBits signedBitLength
  omega

def complexDyadicBits {P : ℕ} (d : ComplexDyadic P) : List Bool :=
  Codec.int d.1.numerator++Codec.int d.2.numerator

theorem complexDyadicBits_length {P B : ℕ} (d : ComplexDyadic P)
    (hd : ‖complexDyadicValue d‖≤(2:ℝ)^B) :
    (complexDyadicBits d).length≤4*(P+B+2) := by
  have hcoords := complexDyadicValue_coordinate_bounds d (B := (2:ℚ)^B) (by simpa using hd)
  have h1 := dyadic_numerator_bits_of_bound d.1 hcoords.1
  have h2 := dyadic_numerator_bits_of_bound d.2 hcoords.2
  simp only [complexDyadicBits,List.length_append,Codec.int_length]
  unfold Dyadic.numeratorBits at h1 h2
  omega

def complexDyadicDataBits {P : ℕ} (xs : List (ComplexDyadic P)) : List Bool :=
  Codec.nat P++Codec.list complexDyadicBits xs

theorem complexDyadicDataBits_length {P B : ℕ} (xs : List (ComplexDyadic P))
    (hxs : ∀ d∈xs, ‖complexDyadicValue d‖≤(2:ℝ)^B) :
    (complexDyadicDataBits xs).length≤8*(xs.length+1)*(P+B+3) := by
  have hl := Codec.list_length_le complexDyadicBits xs (4*(P+B+2))
    (fun d hd => complexDyadicBits_length d (hxs d hd))
  have bits_self (n : ℕ) : unsignedBitLength n≤n := by
    rw [Codec.unsignedBitLength_eq_size]
    exact Nat.size_le.mpr (Nat.lt_two_pow_self (n := n))
  have hP := bits_self P
  have hL := bits_self xs.length
  simp only [complexDyadicDataBits,List.length_append,Codec.nat_length]
  nlinarith only [hl,hP,hL]

#print axioms complexDyadicBits_length
#print axioms complexDyadicDataBits_length

end Maxwell.Continuum
