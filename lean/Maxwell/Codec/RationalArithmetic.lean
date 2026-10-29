import Maxwell.Codec.Output

/-! Arithmetic on literal rational pairs, including bounds on the unreduced
integers that an actual decoder emits. These algebraic lemmas are separate
from the finite Boolean programs implementing integer addition/multiplication. -/

namespace Maxwell.Codec

theorem unsignedBitLength_mul_le (a b : ℕ) :
    unsignedBitLength (a * b) ≤ unsignedBitLength a + unsignedBitLength b := by
  simp only [unsignedBitLength_eq_size]
  apply Nat.size_le.mpr
  rw [pow_add]
  calc
    a * b ≤ a * 2 ^ b.size := Nat.mul_le_mul_left _ (Nat.lt_size_self b).le
    _ < 2 ^ a.size * 2 ^ b.size :=
      Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self a) (by positivity)

theorem unsignedBitLength_add_le (a b : ℕ) :
    unsignedBitLength (a + b) ≤ max (unsignedBitLength a) (unsignedBitLength b) + 1 := by
  simp only [unsignedBitLength_eq_size]
  apply Nat.size_le.mpr
  have ha : a < 2 ^ max a.size b.size :=
    (Nat.lt_size_self a).trans_le (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
  have hb : b < 2 ^ max a.size b.size :=
    (Nat.lt_size_self b).trans_le (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
  rw [pow_succ]
  omega

theorem signedBitLength_mul_nat_le (a : ℤ) (b : ℕ) :
    signedBitLength (a * b) ≤ signedBitLength a + unsignedBitLength b := by
  have hh := unsignedBitLength_mul_le a.natAbs b
  simp only [signedBitLength, Int.natAbs_mul, Int.natAbs_natCast]
  omega

theorem signedBitLength_mul_le (a b : ℤ) :
    signedBitLength (a * b) ≤ signedBitLength a + signedBitLength b := by
  have hh := unsignedBitLength_mul_le a.natAbs b.natAbs
  simp only [signedBitLength, Int.natAbs_mul]
  omega

theorem signedBitLength_add_le (a b : ℤ) :
    signedBitLength (a + b) ≤ max (signedBitLength a) (signedBitLength b) + 1 := by
  have hh := (unsignedBitLength_mono (Int.natAbs_add_le a b)).trans
    (unsignedBitLength_add_le a.natAbs b.natAbs)
  simp only [signedBitLength]
  omega

namespace RationalPair

def zero : RationalPair := ⟨0, 1, by decide⟩

def add (a b : RationalPair) : RationalPair :=
  ⟨a.numerator * b.denominator + b.numerator * a.denominator,
    a.denominator * b.denominator, Nat.mul_pos a.denominator_pos b.denominator_pos⟩

def mul (a b : RationalPair) : RationalPair :=
  ⟨a.numerator * b.numerator,
    a.denominator * b.denominator, Nat.mul_pos a.denominator_pos b.denominator_pos⟩

@[simp] theorem zero_value : zero.value = 0 := by simp [zero, value]

@[simp] theorem add_value (a b : RationalPair) : (add a b).value = a.value + b.value := by
  simp only [add, value, Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
  rw [add_div, mul_div_mul_right _ _ (by exact_mod_cast b.denominator_pos.ne'),
    mul_comm (b.numerator : ℚ), mul_div_mul_left _ _ (by exact_mod_cast a.denominator_pos.ne')]

@[simp] theorem mul_value (a b : RationalPair) : (mul a b).value = a.value * b.value := by
  simp only [mul, value, Int.cast_mul, Nat.cast_mul, mul_div_mul_comm]

theorem zero_short : zero.Short 1 := by
  norm_num [Short, zero, signedBitLength, unsignedBitLength]

theorem add_short {A B : ℕ} {a b : RationalPair}
    (ha : a.Short A) (hb : b.Short B) : (add a b).Short (A + B + 1) := by
  have hl := (signedBitLength_mul_nat_le a.numerator b.denominator).trans
    (Nat.add_le_add ha.1 hb.2)
  have hr := (signedBitLength_mul_nat_le b.numerator a.denominator).trans
    (Nat.add_le_add hb.1 ha.2)
  have hn := signedBitLength_add_le (a.numerator * b.denominator)
    (b.numerator * a.denominator)
  have hd := (unsignedBitLength_mul_le a.denominator b.denominator).trans
    (Nat.add_le_add ha.2 hb.2)
  constructor
  · change signedBitLength (a.numerator * b.denominator + b.numerator * a.denominator) ≤ _
    omega
  · exact hd.trans (Nat.le_succ _)

theorem mul_short {A B : ℕ} {a b : RationalPair}
    (ha : a.Short A) (hb : b.Short B) : (mul a b).Short (A + B) := by
  exact ⟨(signedBitLength_mul_le a.numerator b.numerator).trans (Nat.add_le_add ha.1 hb.1),
    (unsignedBitLength_mul_le a.denominator b.denominator).trans (Nat.add_le_add ha.2 hb.2)⟩

def word (F : Target.FixedPointFormat) (w : F.Word) : RationalPair :=
  ⟨F.numerator w, 2 ^ F.fractionalBits, by positivity⟩

@[simp] theorem word_value (F : Target.FixedPointFormat) (w : F.Word) :
    (word F w).value = F.value w := by
  simp [word, value, Target.FixedPointFormat.value]

theorem word_short (F : Target.FixedPointFormat) (w : F.Word) :
    (word F w).Short (F.width + 1) := by
  have hn := F.numerator_bounds w
  have ha : |F.numerator w| ≤ (2 : ℤ) ^ (F.integerBits + F.fractionalBits) :=
    abs_le.mpr ⟨hn.1, hn.2.le⟩
  rw [← Int.natCast_natAbs] at ha
  have habs : (F.numerator w).natAbs ≤ 2 ^ (F.integerBits + F.fractionalBits) := by
    exact_mod_cast ha
  have hb := unsignedBitLength_mono habs
  rw [Dyadic.denominator_bitLength] at hb
  constructor
  · simp only [word, signedBitLength, Target.FixedPointFormat.width]
    omega
  · simp only [word, Dyadic.denominator_bitLength, Target.FixedPointFormat.width]
    omega

def sumFrom (offset : RationalPair) (terms : List RationalPair) : RationalPair :=
  terms.foldr add offset

theorem sumFrom_value (offset : RationalPair) (terms : List RationalPair) :
    (sumFrom offset terms).value = offset.value + (terms.map value).sum := by
  induction terms with
  | nil => simp [sumFrom]
  | cons term terms ih =>
    simp only [sumFrom, List.foldr_cons, add_value, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    ring

theorem sumFrom_short {A B : ℕ} (offset : RationalPair) (terms : List RationalPair)
    (ha : offset.Short A) (hb : ∀ q ∈ terms, q.Short B) :
    (sumFrom offset terms).Short (A + terms.length * (B + 1)) := by
  induction terms with
  | nil => simpa [sumFrom] using ha
  | cons term terms ih =>
    have ht := hb term (by simp)
    have hs := ih (fun q hq => hb q (by simp [hq]))
    have hh := add_short ht hs
    have heq : B + (A + terms.length * (B + 1)) + 1 =
        A + (terms.length + 1) * (B + 1) := by ring
    simpa only [sumFrom, List.foldr_cons, List.length_cons, heq] using hh

end RationalPair

/-- The literal rational-pair arithmetic specification for the stored local
weighted decoder, including its offset. Every term uses an actual access word. -/
def decoderPairs {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n)
    (messages : D.Messages) (i : Fin n) : RationalPair :=
  RationalPair.sumFrom (RationalPair.canonical (D.offset i))
    (((D.support i).sort).map fun j => RationalPair.mul
      (RationalPair.canonical (D.weight i j)) (RationalPair.word D.format (messages j)))

theorem decoderPairs_value {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n)
    (messages : D.Messages) (i : Fin n) :
    (decoderPairs D messages i).value = D.decode messages i := by
  simp only [decoderPairs, RationalPair.sumFrom_value, RationalPair.canonical_value,
    List.map_map, Function.comp_def, RationalPair.mul_value, RationalPair.word_value,
    Target.WeightedDecoder.decode]
  congr 1
  simpa only [Finset.sort_toFinset] using
    (List.sum_toFinset (fun j : Fin D.sampleCount => D.weight i j * D.format.value (messages j))
      ((D.support i).sort_nodup (· ≤ ·))).symm

/-- The unreduced emitted output still has logarithmic width when stencil
size is constant and all stored coefficients/access words have logarithmic width. -/
theorem decoderPairs_short {ι : Type*} {n B : ℕ} (D : Target.WeightedDecoder ι n)
    (messages : D.Messages) (i : Fin n)
    (hoffset : Source.ShortRational B (D.offset i))
    (hweights : ∀ j ∈ D.support i, Source.ShortRational B (D.weight i j)) :
    (decoderPairs D messages i).Short
      (B + (D.support i).card * (B + D.format.width + 2)) := by
  have hh := RationalPair.sumFrom_short
    (RationalPair.canonical (D.offset i))
    (((D.support i).sort).map fun j => RationalPair.mul
      (RationalPair.canonical (D.weight i j)) (RationalPair.word D.format (messages j)))
    (RationalPair.canonical_short hoffset)
    (B := B + (D.format.width + 1)) (by
      intro q hq
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hq
      exact RationalPair.mul_short
        (RationalPair.canonical_short (hweights j (by simpa using hj)))
        (RationalPair.word_short D.format (messages j)))
  simpa [decoderPairs, Nat.add_assoc] using hh

/-- Concrete unreduced output bytes for the exact stored weighted stencil. -/
def decoderOutput {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n)
    (messages : D.Messages) : List Bool :=
  list RationalPair.encode (List.ofFn (decoderPairs D messages))

theorem decoderOutput_represents {ι : Type*} {n B K : ℕ}
    (D : Target.WeightedDecoder ι n) (messages : D.Messages)
    (hoffset : ∀ i, Source.ShortRational B (D.offset i))
    (hweights : ∀ i j, j ∈ D.support i → Source.ShortRational B (D.weight i j))
    (hsupport : ∀ i, (D.support i).card ≤ K) :
    RepresentsOutput (B + K * (B + D.format.width + 2)) (D.decode messages)
      (decoderOutput D messages) := by
  refine ⟨decoderPairs D messages, rfl, decoderPairs_value D messages, ?_⟩
  intro i
  have hh := decoderPairs_short D messages i (hoffset i) (hweights i)
  have hb := Nat.add_le_add_left
    (Nat.mul_le_mul_right (B + D.format.width + 2) (hsupport i)) B
  exact ⟨hh.1.trans hb, hh.2.trans hb⟩

theorem decoderOutput_length {ι : Type*} {n B K : ℕ}
    (D : Target.WeightedDecoder ι n) (messages : D.Messages)
    (hoffset : ∀ i, Source.ShortRational B (D.offset i))
    (hweights : ∀ i j, j ∈ D.support i → Source.ShortRational B (D.weight i j))
    (hsupport : ∀ i, (D.support i).card ≤ K) :
    (decoderOutput D messages).length ≤ 2 * unsignedBitLength n + 1 +
      n * (4 * (B + K * (B + D.format.width + 2)) + 1) :=
  represents_output_length _ _ (decoderOutput_represents D messages hoffset hweights hsupport)

end Maxwell.Codec
