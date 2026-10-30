import Maxwell.Continuum.RationalWordBounds

/-! Canonical operand-width propagation for the literal rational arithmetic. -/

namespace Maxwell.Continuum.RationalWords
open Maxwell.Cost.RationalAccumulator

structure Width (q : ℚ) (B : ℕ) : Prop where
  num : q.num.natAbs.bits.length≤B
  den : q.den.bits.length≤B

theorem bits_mono {a b : ℕ} (h : a≤b) : a.bits.length≤b.bits.length := by
  simpa only [← Nat.size_eq_bits_len] using Nat.size_le_size h

theorem Width.mono {q : ℚ} {B C : ℕ} (h : Width q B) (hBC : B≤C) : Width q C :=
  ⟨h.num.trans hBC,h.den.trans hBC⟩

theorem Width.mul {q r : ℚ} {B C : ℕ} (hq : Width q B) (hr : Width r C) :
    Width (q*r) (B+C) := by
  constructor
  · rw [Rat.num_mul]
    have h := bits_mono (Int.natAbs_ediv_le_natAbs (q.num*r.num)
      ((q.num*r.num).natAbs.gcd (q.den*r.den)))
    exact h.trans (by
      simpa only [Int.natAbs_mul] using
        (bits_mul_le q.num.natAbs r.num.natAbs).trans (Nat.add_le_add hq.num hr.num))
  · rw [Rat.den_mul]
    exact (bits_mono (Nat.div_le_self (q.den*r.den) _)).trans
      ((bits_mul_le _ _).trans (Nat.add_le_add hq.den hr.den))

theorem Width.neg {q : ℚ} {B : ℕ} (hq : Width q B) : Width (-q) B := by
  constructor
  · simpa only [Rat.neg_num,Int.natAbs_neg] using hq.num
  · simpa only [Rat.neg_den] using hq.den

theorem Width.inv {q : ℚ} {B : ℕ} (hq : Width q B) (hne : q≠0) : Width q⁻¹ B := by
  have hn : q.num≠0 := Rat.num_ne_zero.mpr hne
  constructor
  · simpa only [Rat.num_inv,Int.natAbs_mul,Int.natAbs_sign_of_ne_zero hn,
      one_mul,Int.natAbs_natCast] using hq.den
  · simpa only [Rat.den_inv,ite_eq_right hn] using hq.num

theorem Width.sub {q r : ℚ} {B C : ℕ} (hq : Width q B) (hr : Width r C) :
    Width (q-r) (B+C+1) := by
  have he : q-r=(((q.num*(r.den:ℤ)-r.num*(q.den:ℤ)):ℤ):ℚ)/(q.den*r.den:ℕ) := by
    calc
      _ = (q.num:ℚ)/q.den-(r.num:ℚ)/r.den := by rw [q.num_div_den,r.num_div_den]
      _ = _ := by push_cast; field_simp
  have hleft : (q.num*(r.den:ℤ)).natAbs.bits.length≤B+C := by
    rw [Int.natAbs_mul,Int.natAbs_natCast]
    exact (bits_mul_le _ _).trans (Nat.add_le_add hq.num hr.den)
  have hright : (r.num*(q.den:ℤ)).natAbs.bits.length≤B+C := by
    rw [Int.natAbs_mul,Int.natAbs_natCast]
    have h := (bits_mul_le r.num.natAbs q.den).trans (Nat.add_le_add hr.num hq.den)
    omega
  have hnum : (q.num*(r.den:ℤ)-r.num*(q.den:ℤ)).natAbs.bits.length≤B+C+1 := by
    have h := (bits_mono (Int.natAbs_sub_le (q.num*(r.den:ℤ)) (r.num*(q.den:ℤ)))).trans
      (bits_add_le _ _)
    omega
  have hden := (bits_mul_le q.den r.den).trans (Nat.add_le_add hq.den hr.den)
  rw [he]
  constructor
  · exact (bits_mono (reduced_numerator _ _ (Nat.mul_pos q.den_pos r.den_pos))).trans hnum
  · exact (bits_mono (reduced_denominator _ _ (Nat.mul_pos q.den_pos r.den_pos))).trans (by omega)

theorem Width.add {q r : ℚ} {B C : ℕ} (hq : Width q B) (hr : Width r C) :
    Width (q+r) (B+C+1) := by simpa only [sub_neg_eq_add] using hq.sub hr.neg

theorem width_one : Width 1 1 := by constructor <;> decide
theorem width_two : Width 2 2 := by constructor <;> decide

#print axioms Width.mul
#print axioms Width.sub
#print axioms Width.inv

end Maxwell.Continuum.RationalWords
