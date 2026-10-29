import Maxwell.Cost.RationalAccumulator.Initialize
import Maxwell.Cost.DecoderTerm.Correctness

namespace Maxwell.Cost.DecoderParser.Algebra
open RationalAccumulator
open Codec

/-- The three persistent accumulator words, with their actual denominator. -/
def bankModel (v : ℕ → ℕ) (hd : 0 < v 32) : SplitRational :=
  ⟨v 30, v 31, v 32, hd⟩

/-- Signed magnitude admits either sign for zero, as the machine does. -/
def termModel (v : ℕ → ℕ) (sign : Bool) (hd : 0 < v 34) : RationalPair :=
  ⟨if sign then -(v 33 : ℤ) else v 33, v 34, hd⟩

@[simp] theorem bankModel_value (v : ℕ → ℕ) (hd : 0 < v 32) :
    (bankModel v hd).value = bankValue v := by
  simp [bankModel, SplitRational.value, SplitRational.toPair, RationalPair.value, bankValue]

@[simp] theorem termModel_value (v : ℕ → ℕ) (sign : Bool) (hd : 0 < v 34) :
    (termModel v sign hd).value = termValue v sign := by
  cases sign <;> simp [termModel, RationalPair.value, termValue]

/-- The actual bank update is exactly the split-rational operation. -/
theorem pushed_model (v : ℕ → ℕ) (sign : Bool) (hd : 0 < v 32) (ht : 0 < v 34) :
    bankModel (pushed v sign) (pushed_denominator_pos v sign hd ht) =
      SplitRational.push (bankModel v hd) (termModel v sign ht) := by
  cases sign <;> simp [bankModel, pushed, prepared, selected, SplitRational.push,
    SplitRational.add, SplitRational.ofPair, termModel, Nat.mul_comm, Nat.add_comm]

/-- Initialization binds the parsed signed numerator and denominator to
literal rational-pair initialization, including zero. -/
theorem initialized_model (v : ℕ → ℕ) (q : RationalPair) :
    bankModel (initialized v q) (by simpa using q.denominator_pos) = SplitRational.ofPair q := by
  cases hn : q.numerator with
  | ofNat n =>
      have hnonneg : ¬(n : ℤ) < 0 := by omega
      simp [bankModel, initialized, selected, resetBank, SplitRational.ofPair, hn, hnonneg]
  | negSucc n => simp [bankModel, initialized, selected, resetBank, SplitRational.ofPair, hn]

/-- Equal values and the same literal positive denominator identify the
unreduced pair, so no sign convention for a zero numerator is required. -/
theorem termModel_eq_of_value_denominator (v : ℕ → ℕ) (sign : Bool) (ht : 0 < v 34)
    (q : RationalPair) (hv : termValue v sign = q.value) (hd : v 34 = q.denominator) :
    termModel v sign ht = q := by
  have hh : (termModel v sign ht).value = q.value := (termModel_value v sign ht).trans hv
  have hden : (q.denominator : ℚ) ≠ 0 := by exact_mod_cast q.denominator_pos.ne'
  have hnum : ((termModel v sign ht).numerator : ℚ) = (q.numerator : ℚ) := by
    apply (div_left_inj' hden).mp
    simpa only [RationalPair.value, termModel, hd] using hh
  have hn : (termModel v sign ht).numerator = q.numerator := by exact_mod_cast hnum
  cases q
  simp only [termModel] at hn ⊢
  cases hn
  cases hd
  rfl

/-- Machine-produced fixed-point products bind to the actual unreduced
weight/access-word product, not merely to a rationally equal fraction. -/
theorem fixedPoint_termModel (F : Target.FixedPointFormat) (w : F.Word) (q : ℚ)
    (sample : List Bool) (hsample : addressValue sample = w.val) (v : ℕ → ℕ) :
    let bank := DecoderTerm.termBank v
      (DecoderTerm.magnitude sample (2^(F.integerBits+F.fractionalBits))*q.num.natAbs)
      ((2^F.fractionalBits)*q.den)
    termModel bank (Bool.xor
      (SignedDifference.sign sample (2^(F.integerBits+F.fractionalBits)).bits)
      (decide (q.num < 0))) (by
        exact Nat.mul_pos (by positivity) q.pos) =
      RationalPair.mul (RationalPair.canonical q) (RationalPair.word F w) := by
  dsimp
  apply termModel_eq_of_value_denominator
  · simpa only [termValue, DecoderTerm.termBank, Function.update_self,
      Function.update_of_ne (by decide : (33 : ℕ) ≠ 34), DecoderTerm.signed,
      RationalPair.mul_value, RationalPair.canonical_value, RationalPair.word_value] using
        DecoderTerm.fixedPoint_value F w q sample hsample
  · simp [DecoderTerm.termBank, RationalPair.mul, RationalPair.canonical,
      RationalPair.word, Nat.mul_comm]

/-- Actual bit lengths of the persistent three-word accumulator. -/
def CoreShort (B : ℕ) (v : ℕ → ℕ) : Prop :=
  (v 30).bits.length ≤ B ∧ (v 31).bits.length ≤ B ∧ (v 32).bits.length ≤ B

theorem coreShort_iff (B : ℕ) (v : ℕ → ℕ) (hd : 0 < v 32) :
    CoreShort B v ↔ (bankModel v hd).Short B := by
  simp only [CoreShort, SplitRational.Short, bankModel,
    unsignedBitLength_eq_size, Nat.size_eq_bits_len]

/-- Each fresh term contributes only its own width plus one carry bit. -/
theorem pushed_coreShort (v : ℕ → ℕ) (sign : Bool) (A B : ℕ)
    (hd : 0 < v 32) (ht : 0 < v 34) (hv : CoreShort A v)
    (hq : (termModel v sign ht).Short B) :
    CoreShort (A + B + 1) (pushed v sign) := by
  apply (coreShort_iff _ _ (pushed_denominator_pos v sign hd ht)).mpr
  rw [pushed_model v sign hd ht]
  exact SplitRational.push_short ((coreShort_iff _ _ hd).mp hv) hq

/-- Full-bank width bound for a fresh term, without doubling the previous
accumulator width. Tapes33/34 keep that term and tape36 becomes zero. -/
theorem pushed_bits_linear (v : ℕ → ℕ) (sign : Bool) (A B : ℕ)
    (hv : CoreShort A v) (h33 : (v 33).bits.length ≤ B) (h34 : (v 34).bits.length ≤ B)
    (h35 : (v 35).bits.length ≤ A + B + 1) :
    ∀ i, 30 ≤ i → i ≤ 36 → (pushed v sign i).bits.length ≤ A + B + 1 := by
  have hprod (a b : ℕ) (ha : a.bits.length ≤ A) (hb : b.bits.length ≤ B) :
      (a*b).bits.length ≤ A+B := (bits_mul_le a b).trans (Nat.add_le_add ha hb)
  have hp30 := hprod (v 30) (v 34) hv.1 h34
  have hp31 := hprod (v 31) (v 34) hv.2.1 h34
  have hp32 := hprod (v 32) (v 34) hv.2.2 h34
  have hp33 := hprod (v 32) (v 33) hv.2.2 h33
  have hp := bits_add_le (v 32 * v 33) (v 30 * v 34)
  have hn := bits_add_le (v 32 * v 33) (v 31 * v 34)
  intro i hi hi'
  interval_cases i <;> cases sign <;>
    simp [pushed, prepared, selected, Nat.mul_comm] at * <;> omega

/-- The bank transition induced by one literal rational term. This uses the
same term-bank assignment and push recurrence as the verified machine. -/
def pushPair (v : ℕ → ℕ) (q : RationalPair) : ℕ → ℕ :=
  pushed (DecoderTerm.termBank v q.numerator.natAbs q.denominator) (decide (q.numerator < 0))

theorem pushPair_denominator_pos (v : ℕ → ℕ) (q : RationalPair) (hd : 0 < v 32) :
    0 < pushPair v q 32 := by
  apply pushed_denominator_pos
  · simpa [DecoderTerm.termBank] using hd
  · simpa [DecoderTerm.termBank] using q.denominator_pos

theorem pushPair_model (v : ℕ → ℕ) (q : RationalPair) (hd : 0 < v 32) :
    bankModel (pushPair v q) (pushPair_denominator_pos v q hd) =
      SplitRational.push (bankModel v hd) q := by
  unfold pushPair
  rw [pushed_model _ _ (by simpa [DecoderTerm.termBank] using hd)
    (by simpa [DecoderTerm.termBank] using q.denominator_pos)]
  have ht : termModel (DecoderTerm.termBank v q.numerator.natAbs q.denominator)
      (decide (q.numerator < 0)) (by simpa [DecoderTerm.termBank] using q.denominator_pos) = q := by
    cases hn : q.numerator with
    | ofNat n =>
      have hnonneg : ¬(n : ℤ) < 0 := by omega
      cases q
      simp_all [termModel, DecoderTerm.termBank]
    | negSucc n =>
      cases q
      simp_all [termModel, DecoderTerm.termBank]
      omega
  rw [ht]
  rfl

theorem foldl_pushPair_denominator_pos (v : ℕ → ℕ) (terms : List RationalPair) (hd : 0 < v 32) :
    0 < terms.foldl pushPair v 32 := by
  induction terms generalizing v with
  | nil => exact hd
  | cons q qs ih => exact ih (pushPair v q) (pushPair_denominator_pos v q hd)

theorem foldl_pushPair_model (v : ℕ → ℕ) (terms : List RationalPair) (hd : 0 < v 32) :
    bankModel (terms.foldl pushPair v) (foldl_pushPair_denominator_pos v terms hd) =
      terms.foldl SplitRational.push (bankModel v hd) := by
  induction terms generalizing v with
  | nil => rfl
  | cons q qs ih =>
    have hh := ih (pushPair v q) (pushPair_denominator_pos v q hd)
    rw [pushPair_model v q hd] at hh
    exact hh

/-- Linear accumulator growth for an arbitrary sequence of actual bank
updates; no repeated uniform-width doubling is used. -/
theorem foldl_pushPair_coreShort (v : ℕ → ℕ) (terms : List RationalPair) (A B : ℕ)
    (hd : 0 < v 32) (hv : CoreShort A v) (ht : ∀ q ∈ terms, q.Short B) :
    CoreShort (A + terms.length * (B + 1)) (terms.foldl pushPair v) := by
  apply (coreShort_iff _ _ (foldl_pushPair_denominator_pos v terms hd)).mpr
  rw [foldl_pushPair_model]
  exact SplitRational.foldl_push_short (bankModel v hd) terms ((coreShort_iff _ _ hd).mp hv) ht

/-- Parsed offset followed by the machine's term updates represents the
same exact rational sum used by the public decoder specification. -/
theorem initialized_foldl_model (v : ℕ → ℕ) (offset : RationalPair) (terms : List RationalPair) :
    bankModel (terms.foldl pushPair (initialized v offset))
      (foldl_pushPair_denominator_pos _ terms (by simpa using offset.denominator_pos)) =
      SplitRational.sumFrom offset terms := by
  rw [foldl_pushPair_model _ _ (by simpa using offset.denominator_pos), initialized_model]
  rfl

theorem initialized_foldl_coreShort (v : ℕ → ℕ) (offset : RationalPair)
    (terms : List RationalPair) (A B : ℕ) (ho : offset.Short A)
    (ht : ∀ q ∈ terms, q.Short B) :
    CoreShort (A + terms.length * (B + 1)) (terms.foldl pushPair (initialized v offset)) := by
  apply (coreShort_iff _ _
    (foldl_pushPair_denominator_pos _ terms (by simpa using offset.denominator_pos))).mpr
  rw [initialized_foldl_model]
  exact SplitRational.sumFrom_short offset terms ho ht

theorem initialized_foldl_value (v : ℕ → ℕ) (offset : RationalPair) (terms : List RationalPair) :
    bankValue (terms.foldl pushPair (initialized v offset)) =
      offset.value + (terms.map RationalPair.value).sum := by
  have h := congrArg SplitRational.value (initialized_foldl_model v offset terms)
  simpa only [bankModel_value, SplitRational.sumFrom_value] using h

/-- The existing term-program postcondition suffices to identify the next
split accumulator exactly, while retaining the literal denominator. -/
theorem pushed_model_of_value_denominator (v : ℕ → ℕ) (sign : Bool)
    (hd : 0 < v 32) (ht : 0 < v 34) (q : RationalPair)
    (hv : termValue v sign = q.value) (hq : v 34 = q.denominator) :
    bankModel (pushed v sign) (pushed_denominator_pos v sign hd ht) =
      SplitRational.push (bankModel v hd) q := by
  rw [pushed_model v sign hd ht, termModel_eq_of_value_denominator v sign ht q hv hq]

theorem initialized_coreShort (v : ℕ → ℕ) (offset : RationalPair) (B : ℕ)
    (h : offset.Short B) : CoreShort B (initialized v offset) := by
  apply (coreShort_iff _ _ (by simpa using offset.denominator_pos)).mpr
  rw [initialized_model]
  exact SplitRational.ofPair_short h

/-- The final signed subtraction adds at most two bits to the three-word
linear bound; this matches the actual emitted unreduced rational pair. -/
theorem bankPair_short (v : ℕ → ℕ) (hd : 0 < v 32) (B : ℕ) (h : CoreShort B v) :
    (bankModel v hd).toPair.Short (B + 2) :=
  SplitRational.toPair_short ((coreShort_iff B v hd).mp h)

end Maxwell.Cost.DecoderParser.Algebra


