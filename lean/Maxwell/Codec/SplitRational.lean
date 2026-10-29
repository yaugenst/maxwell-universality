import Maxwell.Codec.RationalArithmetic

/-! A rational accumulator using two nonnegative numerators and one positive
denominator. Its updates require only natural addition and multiplication;
one final signed difference supplies the emitted numerator. -/

namespace Maxwell.Codec

structure SplitRational where
  positive : ℕ
  negative : ℕ
  denominator : ℕ
  denominator_pos : 0 < denominator

namespace SplitRational

def toPair (a : SplitRational) : RationalPair :=
  ⟨(a.positive : ℤ) - a.negative, a.denominator, a.denominator_pos⟩

def value (a : SplitRational) : ℚ := a.toPair.value

def ofPair (a : RationalPair) : SplitRational :=
  ⟨a.numerator.toNat, (-a.numerator).toNat, a.denominator, a.denominator_pos⟩

@[simp] theorem ofPair_toPair (a : RationalPair) : (ofPair a).toPair = a := by
  cases a
  simp [ofPair, toPair]

@[simp] theorem ofPair_value (a : RationalPair) : (ofPair a).value = a.value := by
  simp [value]

def add (a b : SplitRational) : SplitRational :=
  ⟨a.positive * b.denominator + b.positive * a.denominator,
    a.negative * b.denominator + b.negative * a.denominator,
    a.denominator * b.denominator, Nat.mul_pos a.denominator_pos b.denominator_pos⟩

theorem add_toPair (a b : SplitRational) :
    (add a b).toPair = RationalPair.add a.toPair b.toPair := by
  cases a
  cases b
  simp [add, toPair, RationalPair.add]
  ring

@[simp] theorem add_value (a b : SplitRational) : (add a b).value = a.value + b.value := by
  simp only [value, add_toPair, RationalPair.add_value]

/-- One raw signed term updates the two accumulators without subtraction.
Exactly one of the term's nonnegative parts is nonzero. -/
def push (a : SplitRational) (term : RationalPair) : SplitRational := add a (ofPair term)

@[simp] theorem push_value (a : SplitRational) (term : RationalPair) :
    (push a term).value = a.value + term.value := by simp [push]

def Short (B : ℕ) (a : SplitRational) : Prop :=
  unsignedBitLength a.positive ≤ B ∧ unsignedBitLength a.negative ≤ B ∧
    unsignedBitLength a.denominator ≤ B

theorem ofPair_short {B : ℕ} {a : RationalPair} (h : a.Short B) : (ofPair a).Short B := by
  have hsplit := Int.toNat_add_toNat_neg_eq_natAbs a.numerator
  have hp := unsignedBitLength_mono (show a.numerator.toNat ≤ a.numerator.natAbs by omega)
  have hn := unsignedBitLength_mono (show (-a.numerator).toNat ≤ a.numerator.natAbs by omega)
  simp only [RationalPair.Short, signedBitLength] at h
  exact ⟨by simpa [ofPair] using hp.trans (by omega),
    by simpa [ofPair] using hn.trans (by omega), h.2⟩

theorem add_short {A B : ℕ} {a b : SplitRational} (ha : a.Short A) (hb : b.Short B) :
    (add a b).Short (A + B + 1) := by
  have hpp := (unsignedBitLength_mul_le a.positive b.denominator).trans
    (Nat.add_le_add ha.1 hb.2.2)
  have hpn := (unsignedBitLength_mul_le b.positive a.denominator).trans
    (Nat.add_le_add hb.1 ha.2.2)
  have hnp := (unsignedBitLength_mul_le a.negative b.denominator).trans
    (Nat.add_le_add ha.2.1 hb.2.2)
  have hnn := (unsignedBitLength_mul_le b.negative a.denominator).trans
    (Nat.add_le_add hb.2.1 ha.2.2)
  have hp := unsignedBitLength_add_le (a.positive * b.denominator) (b.positive * a.denominator)
  have hn := unsignedBitLength_add_le (a.negative * b.denominator) (b.negative * a.denominator)
  have hd := (unsignedBitLength_mul_le a.denominator b.denominator).trans
    (Nat.add_le_add ha.2.2 hb.2.2)
  exact ⟨by change unsignedBitLength (_ + _) ≤ _; omega,
    by change unsignedBitLength (_ + _) ≤ _; omega, hd.trans (Nat.le_succ _)⟩

theorem push_short {A B : ℕ} {a : SplitRational} {term : RationalPair}
    (ha : a.Short A) (ht : term.Short B) : (push a term).Short (A + B + 1) :=
  add_short ha (ofPair_short ht)

theorem toPair_short {B : ℕ} {a : SplitRational} (h : a.Short B) : a.toPair.Short (B + 2) := by
  rcases h with ⟨hp, hn, hd⟩
  have habs : ((a.positive : ℤ) - a.negative).natAbs ≤ a.positive + a.negative := by
    simpa only [sub_eq_add_neg, Int.natAbs_natCast, Int.natAbs_neg] using
      Int.natAbs_add_le (a.positive : ℤ) (-(a.negative : ℤ))
  have hh := (unsignedBitLength_mono habs).trans (unsignedBitLength_add_le a.positive a.negative)
  constructor
  · change unsignedBitLength ((a.positive : ℤ) - a.negative).natAbs + 1 ≤ _
    omega
  · exact hd.trans (by omega)

def sumFrom (offset : RationalPair) (terms : List RationalPair) : SplitRational :=
  terms.foldl push (ofPair offset)

theorem foldl_push_value (a : SplitRational) (terms : List RationalPair) :
    (terms.foldl push a).value = a.value + (terms.map RationalPair.value).sum := by
  induction terms generalizing a with
  | nil => simp
  | cons q qs ih =>
    simp only [List.foldl_cons, ih, push_value, List.map_cons, List.sum_cons]
    ring

theorem sumFrom_value (offset : RationalPair) (terms : List RationalPair) :
    (sumFrom offset terms).value = offset.value + (terms.map RationalPair.value).sum := by
  simp [sumFrom, foldl_push_value]

theorem foldl_push_short {A B : ℕ} (a : SplitRational) (terms : List RationalPair)
    (ha : a.Short A) (ht : ∀ q ∈ terms, q.Short B) :
    (terms.foldl push a).Short (A + terms.length * (B + 1)) := by
  induction terms generalizing A a with
  | nil => simpa using ha
  | cons q qs ih =>
    have hq := push_short ha (ht q (by simp))
    have hr := ih (push a q) hq (by intro x hx; exact ht x (by simp [hx]))
    have heq : A + B + 1 + qs.length * (B + 1) = A + (qs.length + 1) * (B + 1) := by ring
    simpa only [List.foldl_cons, List.length_cons, heq] using hr

theorem sumFrom_short {A B : ℕ} (offset : RationalPair) (terms : List RationalPair)
    (ho : offset.Short A) (ht : ∀ q ∈ terms, q.Short B) :
    (sumFrom offset terms).Short (A + terms.length * (B + 1)) :=
  foldl_push_short (ofPair offset) terms (ofPair_short ho) ht

end SplitRational

def splitDecoder {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n)
    (messages : D.Messages) (i : Fin n) : SplitRational :=
  SplitRational.sumFrom (RationalPair.canonical (D.offset i))
    (((D.support i).sort).map fun j => RationalPair.mul
      (RationalPair.canonical (D.weight i j)) (RationalPair.word D.format (messages j)))

theorem splitDecoder_value {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n)
    (messages : D.Messages) (i : Fin n) :
    (splitDecoder D messages i).toPair.value = D.decode messages i := by
  have h := decoderPairs_value D messages i
  rw [decoderPairs, RationalPair.sumFrom_value] at h
  exact (SplitRational.sumFrom_value _ _).trans h

theorem splitDecoder_short {ι : Type*} {n B : ℕ} (D : Target.WeightedDecoder ι n)
    (messages : D.Messages) (i : Fin n)
    (hoffset : Source.ShortRational B (D.offset i))
    (hweights : ∀ j ∈ D.support i, Source.ShortRational B (D.weight i j)) :
    (splitDecoder D messages i).toPair.Short
      (B + (D.support i).card * (B + D.format.width + 2) + 2) := by
  have hh := SplitRational.sumFrom_short
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
  simpa [splitDecoder, Nat.add_assoc] using SplitRational.toPair_short hh

def splitDecoderOutput {ι : Type*} {n : ℕ} (D : Target.WeightedDecoder ι n)
    (messages : D.Messages) : List Bool :=
  list RationalPair.encode (List.ofFn fun i => (splitDecoder D messages i).toPair)

theorem splitDecoderOutput_represents {ι : Type*} {n B K : ℕ}
    (D : Target.WeightedDecoder ι n) (messages : D.Messages)
    (hoffset : ∀ i, Source.ShortRational B (D.offset i))
    (hweights : ∀ i j, j ∈ D.support i → Source.ShortRational B (D.weight i j))
    (hsupport : ∀ i, (D.support i).card ≤ K) :
    RepresentsOutput (B + K * (B + D.format.width + 2) + 2) (D.decode messages)
      (splitDecoderOutput D messages) := by
  refine ⟨fun i => (splitDecoder D messages i).toPair, rfl,
    splitDecoder_value D messages, ?_⟩
  intro i
  have hh := splitDecoder_short D messages i (hoffset i) (hweights i)
  have hb := Nat.add_le_add_right (Nat.add_le_add_left
    (Nat.mul_le_mul_right (B + D.format.width + 2) (hsupport i)) B) 2
  exact ⟨hh.1.trans hb, hh.2.trans hb⟩

end Maxwell.Codec
