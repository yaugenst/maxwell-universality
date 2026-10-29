import Maxwell.Cost.RationalCanonical.Euclid
import Maxwell.Codec.Output

namespace Maxwell.Cost.RationalCanonical

def value (negative : Bool) (a b : ℕ) : ℚ :=
  (if negative then -(a:ℚ) else a)/b

theorem value_eq_mkRat (negative : Bool) (a b : ℕ) :
    value negative a b = mkRat (if negative then -(a:ℤ) else a) b := by
  rw [Rat.mkRat_eq_div]
  cases negative <;> simp [value]

theorem value_num (negative : Bool) (a b : ℕ) (hb : 0 < b) :
    (value negative a b).num = if negative then -((a/Nat.gcd a b:ℕ):ℤ) else (a/Nat.gcd a b:ℕ) := by
  have hd : ((Nat.gcd a b : ℕ):ℤ) ∣ (a:ℤ) := Int.ofNat_dvd.mpr (Nat.gcd_dvd_left a b)
  rw [value_eq_mkRat, Rat.num_mkRat, ite_eq_right (Nat.ne_of_gt hb)]
  cases negative <;> simp only [Bool.false_eq_true, ↓reduceIte, Int.natAbs_neg,
    Int.natAbs_natCast, Nat.gcd_comm b a]
  · exact (Int.natCast_ediv a (Nat.gcd a b)).symm
  · rw [Int.neg_ediv_of_dvd hd]
    exact congrArg Neg.neg (Int.natCast_ediv a (Nat.gcd a b)).symm

theorem value_den (negative : Bool) (a b : ℕ) (hb : 0 < b) :
    (value negative a b).den = b/Nat.gcd a b := by
  rw [value_eq_mkRat, Rat.den_mkRat, ite_eq_right (Nat.ne_of_gt hb)]
  cases negative <;> simp [Nat.gcd_comm]

theorem value_num_natAbs (negative : Bool) (a b : ℕ) (hb : 0 < b) :
    (value negative a b).num.natAbs = a/Nat.gcd a b := by
  rw [value_num negative a b hb]
  cases negative <;> simp only [Bool.false_eq_true, ↓reduceIte, Int.natAbs_neg, Int.natAbs_natCast]

theorem value_sign (negative : Bool) (a b : ℕ) (hb : 0 < b) :
    decide ((value negative a b).num < 0) = (negative && decide (a ≠ 0)) := by
  have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_right a hb
  have hdiv : 0 < a/Nat.gcd a b ↔ a ≠ 0 := by
    constructor
    · intro h ha; simp [ha] at h
    · intro ha
      exact Nat.div_pos (Nat.gcd_le_left b (Nat.pos_of_ne_zero ha)) hg
  rw [value_num negative a b hb]
  cases negative
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_and]
    exact decide_eq_false (not_lt.mpr (Int.natCast_nonneg _))
  · simp only [↓reduceIte, Bool.true_and, neg_lt_zero, Int.natCast_pos]
    simp only [hdiv]

theorem canonical_denominator_pos (a b : ℕ) (hb : 0 < b) : 0 < b/Nat.gcd a b := by
  rw [← value_den false a b hb]
  exact Rat.den_pos _

/-- Both actual emitted natural words only shrink under canonicalization. -/
theorem canonical_width (a b B : ℕ) (ha : a.size ≤ B) (hb : b.size ≤ B) :
    (a/Nat.gcd a b).size ≤ B ∧ (b/Nat.gcd a b).size ≤ B := by
  exact ⟨(Nat.size_le_size (Nat.div_le_self _ _)).trans ha,
    (Nat.size_le_size (Nat.div_le_self _ _)).trans hb⟩

end Maxwell.Cost.RationalCanonical
