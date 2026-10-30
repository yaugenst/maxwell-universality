import Maxwell.Continuum.DyadicRounding
import Maxwell.Codec.Bounds
import Maxwell.Realization.Precision

/-! A literal finite signed-word format for moment messages. The encoder
only rounds rational values supplied by the solver; it does not evaluate
an exact field or a real-valued integration oracle. -/

namespace Maxwell.Continuum.FiniteAuxiliary

def momentWordDyadic (P B : ℕ) (w : Fin (2^(B+1))) : Maxwell.Dyadic P :=
  ⟨(w.val : ℤ)-(2 : ℤ)^B⟩

theorem momentWord_bits (B : ℕ) (w : Fin (2^(B+1))) :
    Maxwell.unsignedBitLength w.val ≤ B+1 := by
  rw [Maxwell.Codec.unsignedBitLength_eq_size]
  exact Nat.size_le.mpr w.isLt

def dyadicMomentWord {P : ℕ} (B : ℕ) (d : Maxwell.Dyadic P)
    (hd : d.numerator.natAbs < 2^B) : Fin (2^(B+1)) := by
  refine ⟨(d.numerator+(2 : ℤ)^B).toNat, ?_⟩
  have hn : |d.numerator| < (2 : ℤ)^B := by
    simpa only [Int.natCast_natAbs] using
      (show (d.numerator.natAbs : ℤ) < (2 : ℤ)^B by exact_mod_cast hd)
  have hl : 0 ≤ d.numerator+(2 : ℤ)^B := by
    have := (abs_lt.mp hn).1
    omega
  have hu : d.numerator+(2 : ℤ)^B < (2 : ℤ)^(B+1) := by
    rw [pow_succ]
    have := (abs_lt.mp hn).2
    omega
  exact_mod_cast (show ((d.numerator+(2 : ℤ)^B).toNat : ℤ) < (2 : ℤ)^(B+1) by
    rw [Int.toNat_of_nonneg hl]
    exact hu)

theorem momentWordDyadic_encode {P : ℕ} (B : ℕ) (d : Maxwell.Dyadic P)
    (hd : d.numerator.natAbs < 2^B) :
    momentWordDyadic P B (dyadicMomentWord B d hd) = d := by
  have hn : |d.numerator| < (2 : ℤ)^B := by
    simpa only [Int.natCast_natAbs] using
      (show (d.numerator.natAbs : ℤ) < (2 : ℤ)^B by exact_mod_cast hd)
  have hl : 0 ≤ d.numerator+(2 : ℤ)^B := by
    have := (abs_lt.mp hn).1
    omega
  cases d
  simp only [momentWordDyadic, dyadicMomentWord, Int.toNat_of_nonneg hl,
    add_sub_cancel_right]

theorem roundDyadic_fits {P R : ℕ} {q : ℚ} (hq : |q| ≤ (2 : ℚ)^R) :
    (roundDyadic P q).numerator.natAbs < 2^(R+P+2) := by
  have hn := roundDyadic_numerator_bound P q
  have hp : (0 : ℚ) ≤ (2 : ℚ)^P := by positivity
  have he : |((roundDyadic P q).numerator : ℚ)| < (2 : ℚ)^(R+P+2) := by
    have hm := mul_le_mul_of_nonneg_right hq hp
    have hb : (1 : ℚ) ≤ (2 : ℚ)^(R+P) := one_le_pow₀ (by norm_num)
    rw [pow_add] at hb
    rw [pow_add, pow_add]
    norm_num only [pow_two] at *
    nlinarith only [hn, hm, hb]
  have hi : |(roundDyadic P q).numerator| < (2 : ℤ)^(R+P+2) := by exact_mod_cast he
  rw [← Int.natCast_natAbs] at hi
  exact_mod_cast hi

def roundedMomentWord (P R : ℕ) (q : ℚ) (hq : |q| ≤ (2 : ℚ)^R) :
    Fin (2^(R+P+3)) :=
  dyadicMomentWord (R+P+2) (roundDyadic P q) (roundDyadic_fits hq)

theorem roundedMomentWord_value (P R : ℕ) (q : ℚ) (hq : |q| ≤ (2 : ℚ)^R) :
    momentWordDyadic P (R+P+2) (roundedMomentWord P R q hq) = roundDyadic P q :=
  momentWordDyadic_encode _ _ _

theorem roundedMomentWord_error (P R : ℕ) (q : ℚ) (hq : |q| ≤ (2 : ℚ)^R) :
    |((momentWordDyadic P (R+P+2) (roundedMomentWord P R q hq)).value : ℝ)-q| ≤
      (1/2 : ℝ)^P := by
  rw [roundedMomentWord_value, abs_sub_comm]
  exact roundDyadic_error P q

theorem weighted_round_error (P : ℕ) (v w : ℚ) {x δ : ℝ}
    (hv : |(v : ℝ)| ≤ 1) (hw : |(w : ℝ)-x| ≤ δ)
    (hP : (1/2 : ℝ)^P ≤ δ) :
    |((roundDyadic P (v*w)).value : ℝ)-(v : ℝ)*x| ≤ 2*δ := by
  have hδ : 0 ≤ δ := (abs_nonneg _).trans hw
  have he : |((roundDyadic P (v*w)).value : ℝ)-(v : ℝ)*(w : ℝ)| ≤ δ := by
    simpa only [Rat.cast_mul, abs_sub_comm] using (roundDyadic_error P (v*w)).trans hP
  have hm : |(v : ℝ)*(w : ℝ)-(v : ℝ)*x| ≤ δ := by
    rw [← mul_sub, abs_mul]
    exact (mul_le_mul hv hw (abs_nonneg _) (by norm_num)).trans_eq (one_mul δ)
  exact (abs_sub_le _ ((v : ℝ)*(w : ℝ)) _).trans (by linarith only [he, hm, hδ])

def momentPrecision (δ : ℚ) (hδ : 0 < δ) : ℕ :=
  Maxwell.Realization.precisionBits δ hδ

theorem momentPrecision_spec (δ : ℚ) (hδ : 0 < δ) :
    (1/2 : ℝ)^(momentPrecision δ hδ) ≤ (δ : ℝ) := by
  have h := Maxwell.Realization.precisionUnit_le δ hδ
  rw [Maxwell.Realization.precisionUnit_eq_pow] at h
  unfold momentPrecision
  simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
    (Rat.cast_le (K := ℝ)).mpr h

theorem momentPrecision_log (δ : ℚ) (hδ : 0 < δ) :
    (momentPrecision δ hδ : ℝ) ≤
      1+Real.log ((Maxwell.Realization.precisionBudget δ : ℝ)⁻¹)/Real.log 2 :=
  Maxwell.Realization.precisionBits_le_log δ hδ

#print axioms momentWordDyadic_encode
#print axioms roundedMomentWord_error
#print axioms weighted_round_error
#print axioms momentPrecision_spec

end Maxwell.Continuum.FiniteAuxiliary
