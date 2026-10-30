import Maxwell.Codec.RationalArithmetic
import Maxwell.Cost.RationalAccumulator.Move

/-! Canonical rational widths follow from literal unreduced stored words. -/

namespace Maxwell.Continuum.RationalWords

theorem reduced_numerator (z : ℤ) (d : ℕ) (hd : 0<d) :
    (((z:ℚ)/d).num).natAbs≤z.natAbs := by
  have he : (z:ℚ)/d=Rat.divInt z (d:ℤ) := by simpa using (Rat.divInt_eq_div z (d:ℤ)).symm
  rw [he,Rat.num_divInt,Int.sign_eq_one_of_pos (by exact_mod_cast hd),one_mul]
  exact Int.natAbs_ediv_le_natAbs _ _

theorem reduced_denominator (z : ℤ) (d : ℕ) (hd : 0<d) :
    ((z:ℚ)/d).den≤d := by
  have he : (z:ℚ)/d=Rat.divInt z (d:ℤ) := by simpa using (Rat.divInt_eq_div z (d:ℤ)).symm
  rw [he,Rat.den_divInt,ite_eq_right (by exact_mod_cast hd.ne'),Int.natAbs_natCast]
  exact Nat.div_le_self _ _

theorem parts_width (p n d B : ℕ) (hd : 0<d)
    (hp : p.bits.length≤B) (hn : n.bits.length≤B) (hden : d.bits.length≤B) :
    (((p:ℚ)-n)/d).num.natAbs.bits.length≤B+1 ∧
    (((p:ℚ)-n)/d).den.bits.length≤B := by
  have hz : (((p:ℤ)-n).natAbs).bits.length≤B+1 := by
    have ha := Codec.signedBitLength_add_le (p:ℤ) (-(n:ℤ))
    simp only [signedBitLength,Int.natAbs_neg,Int.natAbs_natCast,
      Codec.unsignedBitLength_eq_size,← Nat.size_eq_bits_len,← sub_eq_add_neg] at ha
    omega
  have hnum := Codec.unsignedBitLength_mono (reduced_numerator ((p:ℤ)-n) d hd)
  have hde := Codec.unsignedBitLength_mono (reduced_denominator ((p:ℤ)-n) d hd)
  simp only [Int.cast_sub,Int.cast_natCast,Codec.unsignedBitLength_eq_size,← Nat.size_eq_bits_len] at hnum hde
  exact ⟨hnum.trans hz,hde.trans hden⟩

theorem parts_rational_bits (p n d B : ℕ) (hd : 0<d)
    (hp : p.bits.length≤B) (hn : n.bits.length≤B) (hden : d.bits.length≤B) :
    rationalBitLength (((p:ℚ)-n)/d)≤2*B+2 := by
  have hh := parts_width p n d B hd hp hn hden
  simp only [rationalBitLength,signedBitLength,Codec.unsignedBitLength_eq_size,← Nat.size_eq_bits_len]
  omega

#print axioms parts_rational_bits

end Maxwell.Continuum.RationalWords
