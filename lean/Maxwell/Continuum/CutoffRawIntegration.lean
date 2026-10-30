import Maxwell.Continuum.CutoffRawArithmetic

/-! The actual unreduced integral evaluator and its polynomial word bounds. -/

namespace Maxwell.Continuum.Calibration.RawCutoff

open RationalDataflow Profile

set_option maxHeartbeats 800000
attribute [local irreducible] encodedCoefficient profileDegree profileWorkBits chebyshevRow

def squareIntegral (j : ℕ) (a b : Parts) : Parts := sum (fun k => integralTerm j k a b) (j+1)

theorem squareIntegral_valid (j : ℕ) (a b : Parts) (ha : a.Valid) (hb : b.Valid) :
    (squareIntegral j a b).Valid :=
  sum_valid _ _ (fun k _ => integralTerm_valid j k a b ha hb)

theorem squareIntegral_value (j : ℕ) (a b : Parts) (ha : a.Valid) (hb : b.Valid) :
    (squareIntegral j a b).value=chebyshevSquareIntegral j a.value b.value := by
  rw [squareIntegral,sum_value _ _ (fun k _ => integralTerm_valid j k a b ha hb)]
  rw [← Fin.sum_univ_eq_sum_range (fun k => (integralTerm j k a b).value) (j+1)]
  unfold chebyshevSquareIntegral
  apply Finset.sum_congr rfl
  intro k _
  exact integralTerm_value j k k.isLt a b ha hb

theorem squareIntegral_width (j : ℕ) {a b : Parts} {W : ℕ}
    (ha : a.Width W) (hb : b.Width W) :
    (squareIntegral j a b).Width (64*(j+1)^2*(W+1)) := by
  have h := sum_width (fun k => integralTerm j k a b) (j+1) (32*(j+1)*(W+1))
    (fun k hk => integralTerm_width j k hk ha hb)
  apply h.mono
  have hj : j+1≤(j+1)^2*(W+1) := by
    have hp : 1≤(j+1)*(W+1) := Nat.succ_le_of_lt (by positivity)
    nlinarith only [hp,Nat.mul_le_mul_left (j+1) hp]
  have hp : 1≤(j+1)^2*(W+1) := Nat.succ_le_of_lt (by positivity)
  nlinarith only [hj,hp]

def ofDyadic {P : ℕ} (d : Dyadic P) : Parts :=
  ⟨d.numerator.toNat,(-d.numerator).toNat,2^P⟩

theorem ofDyadic_valid {P : ℕ} (d : Dyadic P) : (ofDyadic d).Valid := by
  unfold ofDyadic Parts.Valid
  positivity

theorem ofDyadic_value {P : ℕ} (d : Dyadic P) : (ofDyadic d).value=d.value := by
  have hz : ((d.numerator.toNat : ℕ) : ℚ)-(((-d.numerator).toNat : ℕ) : ℚ)=(d.numerator : ℚ) := by
    exact_mod_cast Int.toNat_sub_toNat_neg d.numerator
  unfold ofDyadic Parts.value Dyadic.value
  rw [hz,Nat.cast_pow,Nat.cast_ofNat]

theorem ofDyadic_width {P B : ℕ} (d : Dyadic P) (hn : d.numerator.natAbs.bits.length≤B)
    (hd : (2^P).bits.length≤B) : (ofDyadic d).Width B := by
  have habs := Int.toNat_add_toNat_neg_eq_natAbs d.numerator
  have hp : d.numerator.toNat≤d.numerator.natAbs := by omega
  have hm : (-d.numerator).toNat≤d.numerator.natAbs := by omega
  exact ⟨(RationalWords.bits_mono hp).trans hn,(RationalWords.bits_mono hm).trans hn,hd⟩

def coefficient (N j : ℕ) : Parts := ofDyadic (encodedCoefficient N j)

theorem coefficient_valid (N j : ℕ) : (coefficient N j).Valid := by
  exact ofDyadic_valid _

theorem coefficient_value (N j : ℕ) : (coefficient N j).value=(encodedCoefficient N j).value := by
  exact ofDyadic_value _

theorem coefficient_width (N j : ℕ) (hj : j<profileDegree N) :
    (coefficient N j).Width (272*(N+1)) := by
  have hn := encodedCoefficient_numerator_bits N j hj
  have hd := encodedCoefficient_denominator_bits N
  simp only [Dyadic.numeratorBits,signedBitLength,Codec.unsignedBitLength_eq_size,
    ← Nat.size_eq_bits_len] at hn hd
  exact ofDyadic_width _ (by omega) (by omega)

def integral (N : ℕ) (a b : Parts) : Parts :=
  sum (fun j => (coefficient N j).mul (squareIntegral j a b)) (profileDegree N)

theorem integral_valid (N : ℕ) (a b : Parts) (ha : a.Valid) (hb : b.Valid) :
    (integral N a b).Valid :=
  sum_valid _ _ (fun j _ => Parts.mul_valid (coefficient_valid N j) (squareIntegral_valid j a b ha hb))

theorem integral_value (N : ℕ) (a b : Parts) (ha : a.Valid) (hb : b.Valid) :
    (integral N a b).value=cutoffIntegralApprox N a.value b.value := by
  unfold integral cutoffIntegralApprox
  rw [sum_value _ _ (fun j _ => Parts.mul_valid (coefficient_valid N j) (squareIntegral_valid j a b ha hb))]
  simp only [Parts.mul_value,coefficient_value,squareIntegral_value _ _ _ ha hb]

def integralWidth (N W : ℕ) : ℕ :=
  profileDegree N*(272*(N+1)+64*(profileDegree N+1)^2*(W+1)+2)+1

theorem integral_width (N : ℕ) {a b : Parts} {W : ℕ} (ha : a.Width W) (hb : b.Width W) :
    (integral N a b).Width (integralWidth N W) := by
  apply sum_width
  intro j hj
  apply ((coefficient_width N j hj).mul (squareIntegral_width j ha hb)).mono
  gcongr

theorem integralWidth_polynomial (N W : ℕ) :
    integralWidth N W≤2^103*(N+1)^6*(W+1) := by
  have hD := profileDegree_bound N
  have hN2 : 1≤(N+1)^2 := one_le_pow₀ (by omega)
  have hDp : profileDegree N+1≤2^31*(N+1)^2 := by nlinarith only [hD,hN2]
  have hs := Nat.pow_le_pow_left hDp 2
  have hN4 : N+1≤(N+1)^4 := le_self_pow₀ (by omega : 1≤N+1) (by decide : (4 : ℕ)≠0)
  have hm : 1≤(N+1)^4*(W+1) := Nat.succ_le_of_lt (by positivity)
  have hn : N+1≤(N+1)^4*(W+1) := hN4.trans (Nat.le_mul_of_pos_right _ (by omega))
  have ht : 272*(N+1)+64*(profileDegree N+1)^2*(W+1)+2≤2^70*(N+1)^4*(W+1) := by
    have hh := Nat.mul_le_mul_right (64*(W+1)) hs
    nlinarith only [hh,hn,hm]
  have hp := Nat.mul_le_mul hD ht
  have hbig : 1≤(N+1)^6*(W+1) := Nat.succ_le_of_lt (by positivity)
  unfold integralWidth
  nlinarith only [hp,hbig]

#print axioms integral_value
#print axioms integral_width
#print axioms integralWidth_polynomial

end Maxwell.Continuum.Calibration.RawCutoff
