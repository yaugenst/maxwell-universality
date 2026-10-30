import Maxwell.Continuum.FiniteAuxiliaryMessageRange

/-! Literal padded Boolean serialization for the fixed signed moment
words, with exact decoding and logarithmic resource bounds. -/

namespace Maxwell.Continuum.FiniteAuxiliary

def momentWordSerial (B : ℕ) (w : Fin (2^(B+1))) : List Bool :=
  w.val.bits ++ List.replicate (B+1-w.val.bits.length) false

private theorem bitsValue_false (k : ℕ) :
    Maxwell.Codec.bitsValue (List.replicate k false) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, Maxwell.Codec.bitsValue, ih]

private theorem bitsValue_append_false (xs : List Bool) (k : ℕ) :
    Maxwell.Codec.bitsValue (xs ++ List.replicate k false) = Maxwell.Codec.bitsValue xs := by
  induction xs with
  | nil => simpa only [List.nil_append, Maxwell.Codec.bitsValue] using bitsValue_false k
  | cons b xs ih => simp only [List.cons_append, Maxwell.Codec.bitsValue, ih]

theorem momentWordSerial_length (B : ℕ) (w : Fin (2^(B+1))) :
    (momentWordSerial B w).length = B+1 := by
  have hw := momentWord_bits B w
  rw [Maxwell.Codec.unsignedBitLength_eq_size, ← Nat.size_eq_bits_len] at hw
  simp only [momentWordSerial, List.length_append, List.length_replicate]
  omega

theorem momentWordSerial_value (B : ℕ) (w : Fin (2^(B+1))) :
    Maxwell.Codec.bitsValue (momentWordSerial B w) = w.val := by
  rw [momentWordSerial, bitsValue_append_false, Maxwell.Codec.bitsValue_bits]

theorem momentWordSerial_injective (B : ℕ) : Function.Injective (momentWordSerial B) := by
  intro v w h
  apply Fin.ext
  simpa only [momentWordSerial_value] using congrArg Maxwell.Codec.bitsValue h

def momentStream {J : ℕ} (B : ℕ) (w : Fin J → Fin (2^(B+1))) : List Bool :=
  (List.ofFn w).flatMap (momentWordSerial B)

theorem momentStream_length {J : ℕ} (B : ℕ) (w : Fin J → Fin (2^(B+1))) :
    (momentStream B w).length = J*(B+1) := by
  have hs (xs : List (Fin (2^(B+1)))) :
      (xs.flatMap (momentWordSerial B)).length = xs.length*(B+1) := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      simp only [List.flatMap_cons, List.length_append, momentWordSerial_length,
        ih, List.length_cons]
      ring
  simpa only [momentStream, List.length_ofFn] using hs (List.ofFn w)

theorem messageRangeBits_le {G : ℚ} {m a b : ℕ}
    (hG : G ≤ (2 : ℚ)^a) (hm : m ≤ 2^b) :
    messageRangeBits G m ≤ a+b+3 := by
  apply Nat.clog_le_of_le_pow
  apply Nat.ceil_le.mpr
  have hmQ : (m : ℚ) ≤ (2 : ℚ)^b := by exact_mod_cast hm
  have ht := mul_le_mul hG hmQ (by positivity : (0 : ℚ) ≤ m) (by positivity)
  have hh := mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℚ) ≤ 8)
  push_cast
  calc
    8*G*(m : ℚ) ≤ 8*((2 : ℚ)^a*(2 : ℚ)^b) := by nlinarith only [hh]
    _ = _ := by rw [pow_add, pow_add]; norm_num; ring

theorem momentPrecision_le_binary (δ : ℚ) (hδ : 0 < δ) {c : ℕ}
    (hc : (1/2 : ℚ)^c ≤ δ) : momentPrecision δ hδ ≤ c := by
  unfold momentPrecision Maxwell.Realization.precisionBits Maxwell.Realization.geometricSteps
  apply Nat.find_min'
  exact le_min (pow_le_one₀ (by norm_num) (by norm_num)) hc

theorem moment_word_width_binary {G δ : ℚ} {m a b c : ℕ}
    (hG : G ≤ (2 : ℚ)^a) (hm : m ≤ 2^b)
    (hδ : 0 < δ) (hc : (1/2 : ℚ)^c ≤ δ) :
    messageRangeBits G m+momentPrecision δ hδ+3 ≤ a+b+c+6 := by
  have hr := messageRangeBits_le hG hm
  have hp := momentPrecision_le_binary δ hδ hc
  omega

#print axioms momentWordSerial_value
#print axioms momentStream_length
#print axioms moment_word_width_binary

end Maxwell.Continuum.FiniteAuxiliary
