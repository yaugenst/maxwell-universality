import Maxwell.Continuum.RationalDataflowParts
import Maxwell.Continuum.CutoffIntegralWidths

/-! Unreduced finite arithmetic for cutoff integration. These bounds concern
the actual numerator channels and denominators, not reduced rational values. -/

namespace Maxwell.Continuum.Calibration.RawCutoff

open RationalDataflow Profile

def power (x : Parts) : ℕ → Parts
  | 0 => Parts.literal 1
  | n+1 => (power x n).mul x

def sum (f : ℕ → Parts) : ℕ → Parts
  | 0 => Parts.literal 0
  | n+1 => (sum f n).add (f n)

theorem power_valid (x : Parts) (hx : x.Valid) (n : ℕ) : (power x n).Valid := by
  induction n with
  | zero => exact Parts.literal_valid 1
  | succ n ih => exact Parts.mul_valid ih hx

theorem power_value (x : Parts) (n : ℕ) : (power x n).value=x.value^n := by
  induction n with
  | zero => simp only [power,Parts.literal_value,pow_zero]
  | succ n ih => rw [power,Parts.mul_value,ih,pow_succ]

theorem power_width {x : Parts} {B : ℕ} (hx : x.Width B) (n : ℕ) :
    (power x n).Width (n*(B+1)+1) := by
  induction n with
  | zero => simpa only [power,zero_mul,zero_add] using Parts.literal_width RationalWords.width_one
  | succ n ih =>
    change ((power x n).mul x).Width _
    convert ih.mul hx using 1
    ring

theorem sum_valid (f : ℕ → Parts) (n : ℕ) (hf : ∀ j<n, (f j).Valid) :
    (sum f n).Valid := by
  induction n with
  | zero => exact Parts.literal_valid 0
  | succ n ih => exact Parts.add_valid (ih (fun j hj => hf j (by omega))) (hf n (by omega))

theorem sum_value (f : ℕ → Parts) (n : ℕ) (hf : ∀ j<n, (f j).Valid) :
    (sum f n).value=∑ j∈Finset.range n, (f j).value := by
  induction n with
  | zero => simp only [sum,Parts.literal_value,Finset.range_zero,Finset.sum_empty]
  | succ n ih =>
    rw [sum,Parts.add_value _ _ (sum_valid f n (fun j hj => hf j (by omega))) (hf n (by omega)),
      ih (fun j hj => hf j (by omega)),Finset.sum_range_succ]

theorem sum_width (f : ℕ → Parts) (n B : ℕ) (hf : ∀ j<n, (f j).Width B) :
    (sum f n).Width (n*(B+1)+1) := by
  induction n with
  | zero => simpa only [sum,zero_mul,zero_add] using Parts.literal_width RationalWords.width_zero'
  | succ n ih =>
    change ((sum f n).add (f n)).Width _
    convert (ih (fun j hj => hf j (by omega))).add (hf n (by omega)) using 1
    ring

def integralTerm (j k : ℕ) (a b : Parts) : Parts :=
  let c := if h : k<j+1 then (chebyshevRow (j+1) j).get ⟨k,h⟩ else 0
  (((Parts.literal (c : ℚ)).mul (power (Parts.literal 4) k)).mul
    ((power b (2*k+1)).sub (power a (2*k+1)))).mul
      ((Parts.literal (2*(k : ℚ)+1)).inverse)

theorem integralTerm_valid (j k : ℕ) (a b : Parts) (ha : a.Valid) (hb : b.Valid) :
    (integralTerm j k a b).Valid := by
  unfold integralTerm
  exact Parts.mul_valid (Parts.mul_valid
    (Parts.mul_valid (Parts.literal_valid _) (power_valid _ (Parts.literal_valid _) _))
    (Parts.sub_valid (power_valid b hb _) (power_valid a ha _)))
      (Parts.inverse_valid (by rw [Parts.literal_value]; positivity))

theorem integralTerm_value (j k : ℕ) (hk : k<j+1) (a b : Parts) (ha : a.Valid) (hb : b.Valid) :
    (integralTerm j k a b).value=((chebyshevRow (j+1) j).get ⟨k,hk⟩ : ℚ)*(4 : ℚ)^k*
      (b.value^(2*k+1)-a.value^(2*k+1))/(2*(k : ℚ)+1) := by
  unfold integralTerm
  have hden : (Parts.literal (2*(k : ℚ)+1)).value≠0 := by rw [Parts.literal_value]; positivity
  simp only [dite_eq_left hk,Parts.mul_value,Parts.literal_value,power_value,
    Parts.sub_value _ _ (power_valid b hb _) (power_valid a ha _),
    Parts.inverse_value _ (Parts.literal_valid _) hden]
  rfl

theorem integralTerm_width (j k : ℕ) (hk : k<j+1) {a b : Parts} {W : ℕ}
    (ha : a.Width W) (hb : b.Width W) :
    (integralTerm j k a b).Width (32*(j+1)*(W+1)) := by
  have hc := Parts.literal_width (chebyshevRow_width (j+1) j ⟨k,hk⟩)
  have h4 := Parts.literal_width (show RationalWords.Width (4 : ℚ) 3 by constructor <;> decide)
  have hd : (Parts.literal (2*(k : ℚ)+1)).Width (2*k+2) := by
    apply Parts.literal_width
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using
      RationalWords.width_nat (2*k+1)
  have h := ((hc.mul (power_width h4 k)).mul
    ((power_width hb (2*k+1)).sub (power_width ha (2*k+1)))).mul hd.inverse
  unfold integralTerm
  rw [dite_eq_left hk]
  apply h.mono
  have hkw := Nat.mul_le_mul_right (W+1) (show k≤j by omega)
  nlinarith only [hkw,show k≤j by omega,Nat.zero_le (j*W)]

#print axioms power_width
#print axioms integralTerm_width

end Maxwell.Continuum.Calibration.RawCutoff
