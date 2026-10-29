import Maxwell.Cost.CalibrationMatrix.Dot
import Maxwell.Cost.IntegerNormSquare.Magnitude
import Maxwell.Defect.IntegerNormalization

namespace Maxwell.Cost.RationalNormalize

open Structured CalibrationMatrix RationalAccumulator
open scoped BigOperators

def integerVector {n : ℕ} (d : Data n n) (i : Fin n) : ℤ :=
  (addressValue (d.vectorPositive.get i) : ℤ) - addressValue (d.vectorNegative.get i)

def normPositive {n : ℕ} (d : Data n n) : ℕ := ∑ j, d.rowPositive 0 (by omega) j

def normNegative {n : ℕ} (d : Data n n) : ℕ := ∑ j, d.rowNegative 0 (by omega) j

/-- A self-dot product has nonnegative signed value equal to the sum of
the squared integer coordinates, including channels with cancellation. -/
theorem self_dot_signed_value {n : ℕ} (d : Data n n)
    (hp : d.matrixPositive = d.vectorPositive) (hn : d.matrixNegative = d.vectorNegative) :
    (normPositive d : ℤ) - normNegative d =
      (Maxwell.Defect.integerNormSq (integerVector d) : ℤ) := by
  simp only [normPositive, normNegative, Maxwell.Defect.integerNormSq, Nat.cast_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi : rowIndex 0 (show 0 + n ≤ n by omega) i = i := by ext; simp [rowIndex]
  simp only [Data.rowPositive, Data.rowNegative, Data.positiveTerm, Data.negativeTerm,
    hi, hp, hn, integerVector, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Int.natCast_natAbs,
    sq_abs]
  ring

theorem self_dot_magnitude {n : ℕ} (d : Data n n)
    (hp : d.matrixPositive = d.vectorPositive) (hn : d.matrixNegative = d.vectorNegative) :
    IntegerNormSquare.magnitude (normPositive d) (normNegative d) =
      Maxwell.Defect.integerNormSq (integerVector d) := by
  simpa only [IntegerNormSquare.magnitude, Int.natAbs_natCast] using
    congrArg Int.natAbs (self_dot_signed_value d hp hn)

def normValues {n : ℕ} (d : Data n n) : ℕ → ℕ :=
  Function.update (dotValues (normPositive d) (normNegative d)) 34
    (Maxwell.Defect.integerNormSq (integerVector d))

def normCode : Code := .seq dotCode IntegerNormSquare.magnitudeCode

def normCost (n B countLength : ℕ) : ℕ := dotCost n B countLength + 300 * (2 * B + 4)

/-- Common preservation contract for indexed array reads and signed
arithmetic. Only the documented loop counters and working registers vary. -/
def NormFrame (s t : BitRAMState) : Prop :=
  t.memory = s.memory ∧ t.inputHead = s.inputHead ∧ t.randomCursor = s.randomCursor ∧
  t.output = s.output ∧
  (∀ i, (i = 4 ∨ 10 ≤ i) → (i < 30 ∨ 36 < i) → i ≠ 102 → i ≠ 103 → i ≠ 106 →
    t.tapes i = s.tapes i) ∧
  (∀ i, 15 ≤ i → i ≠ 23 → i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 28 →
    i ≠ 29 → i ≠ 35 → t.registers i = s.registers i)

theorem NormFrame.trans {s t u : BitRAMState} (h : NormFrame s t) (k : NormFrame t u) :
    NormFrame s u := by
  rcases h with ⟨hm, hi, hr, ho, ht, hg⟩
  rcases k with ⟨km, ki, kr, ko, kt, kg⟩
  exact ⟨km.trans hm, ki.trans hi, kr.trans hr, ko.trans ho,
    fun i hi hj hk hl hm => (kt i hi hj hk hl hm).trans (ht i hi hj hk hl hm),
    fun i hi h23 h24 h25 h26 h27 h28 h29 h35 =>
      (kg i hi h23 h24 h25 h26 h27 h28 h29 h35).trans
        (hg i hi h23 h24 h25 h26 h27 h28 h29 h35)⟩

theorem NormFrame.of_loop {s t : BitRAMState} (h : LoopFrame s t) : NormFrame s t :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    fun i hi _ h24 h25 h26 h27 h28 h29 _ => h.2.2.2.2.2 i hi h24 h25 h26 h27 h28 h29⟩

theorem NormFrame.of_arithmetic {s t : BitRAMState} (h : DyadicSqrt.Frame s t) :
    NormFrame s t :=
  ⟨h.2.2.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1,
    fun i hi hb _ _ _ => h.2.2.2.2.2.1 i (by omega) hb,
    fun i hi h23 h24 h25 h26 h27 _ _ h35 => h.2.2.2.2.2.2 i hi h23 h24 h25 h26 h27 h35⟩

theorem stored_of_normFrame {m n : ℕ} {d : Data m n} {s t : BitRAMState}
    (h : Stored d s) (hf : NormFrame s t) : Stored d t := by
  have keep (i : ℕ) (hi : i = 100 ∨ i = 101 ∨ 110 ≤ i) : t.tapes i = s.tapes i :=
    hf.2.2.2.2.1 i (Or.inr (by omega)) (Or.inr (by omega)) (by omega) (by omega) (by omega)
  exact ⟨BankArray.word_of_eq (keep 100 (by omega)) h.width,
    BankArray.word_of_eq (keep 101 (by omega)) h.clock,
    BankArray.word_of_eq (keep 110 (by omega)) h.matrixPositiveBase,
    BankArray.word_of_eq (keep 111 (by omega)) h.matrixNegativeBase,
    BankArray.word_of_eq (keep 112 (by omega)) h.vectorPositiveBase,
    BankArray.word_of_eq (keep 113 (by omega)) h.vectorNegativeBase,
    by simpa only [hf.1] using h.matrixPositive,
    by simpa only [hf.1] using h.matrixNegative,
    by simpa only [hf.1] using h.vectorPositive,
    by simpa only [hf.1] using h.vectorNegative⟩

private theorem ready_of_signed_arithmetic {s t : BitRAMState} {v w : ℕ → ℕ}
    (h : Ready s v) (hb : Bank t w) (hs : Scratch t 0) (hf : DyadicSqrt.Frame s t) :
    Ready t w := by
  have keep (i : ℕ) (hi : i < 10) (hi' : 4 ≤ i) : t.tapes i = s.tapes i :=
    hf.2.2.2.2.2.1 i hi' (Or.inl (by omega))
  exact ⟨hb, ⟨hs.1, (zero_word_iff_blank t 1).mp hs.2.1, hs.2.2.1, hs.2.2.2,
    blank_of_eq (keep 5 (by omega) (by omega)) h.2.1.2.2.2.2.1,
    blank_of_eq (keep 6 (by omega) (by omega)) h.2.1.2.2.2.2.2.1,
    blank_of_eq (keep 8 (by omega) (by omega)) h.2.1.2.2.2.2.2.2.1,
    blank_of_eq (keep 9 (by omega) (by omega)) h.2.1.2.2.2.2.2.2.2⟩,
    blank_of_eq (keep 7 (by omega) (by omega)) h.2.2⟩

/-- The actual indexed self-dot loop followed by the magnitude routine
returns the exact integer norm square in tape 34, with all scratch restored. -/
theorem norm_executes {n : ℕ} (d : Data n n) (B : ℕ)
    (hpositive : d.matrixPositive = d.vectorPositive)
    (hnegative : d.matrixNegative = d.vectorNegative)
    (hsized : d.Sized B) (hn : n < 2^B)
    (hp : (normPositive d).bits.length ≤ B) (hneg : (normNegative d).bits.length ≤ B)
    (input : List Bool) (tape : ℕ → Bool) (mi vi countWord : List Bool)
    (hmi : addressValue mi = 0) (hvi : addressValue vi = 0)
    (hml : mi.length ≤ B) (hvl : vi.length ≤ B) (hcount : addressValue countWord = n)
    (countOrigin : ℤ) (s : Store) (hcountWord : s.val.tapes 106 = BitTape.shifted countWord countOrigin)
    (hready : Ready s.val (dotValues 0 0)) (hdata : Stored d s.val) (hindices : Indices s.val mi vi) :
    ∃ cost, ∃ t : Store, ∃ finalMatrixIndex finalVectorIndex : List Bool,
      cost ≤ normCost n B countWord.length ∧ Executes input tape normCode cost s t ∧
      addressValue finalMatrixIndex = n ∧ addressValue finalVectorIndex = n ∧
      finalMatrixIndex.length ≤ B ∧ finalVectorIndex.length ≤ B ∧
      Indices t.val finalMatrixIndex finalVectorIndex ∧ Stored d t.val ∧
      Ready t.val (normValues d) ∧ Blank t.val 106 ∧ NormFrame s.val t.val := by
  obtain ⟨dcost, a, fm, fv, hdcost, hed, hfm, hfv, hfml, hfvl, hai, had, har, ha106, haf⟩ :=
    dot d 0 B (by omega) hsized hn hp hneg input tape mi vi countWord hmi hvi hml hvl
      hcount countOrigin s hcountWord hready hdata hindices
  obtain ⟨mcost, t, hmcost, hem, htb, htr, htf⟩ := IntegerNormSquare.store_magnitude
    input tape (dotValues (normPositive d) (normNegative d)) a har.1 har.arithmetic
    (by simp [dotValues])
  have hb : Bank t.val (normValues d) := by
    simpa only [normValues, dotValues, Function.update_self, Function.update_of_ne (show (30 : ℕ) ≠ 31 by omega),
      self_dot_magnitude d hpositive hnegative] using htb
  have keep (i : ℕ) (hi : 36 < i) : t.val.tapes i = a.val.tapes i :=
    htf.2.2.2.2.2.1 i (by omega) (Or.inr hi)
  have hframe := (NormFrame.of_loop haf).trans (NormFrame.of_arithmetic htf)
  refine ⟨dcost + mcost, t, fm, fv, ?_, hed.seq hem, by simpa using hfm, hfv, hfml, hfvl,
    ⟨BankArray.word_of_eq (keep 102 (by omega)) hai.1,
      BankArray.word_of_eq (keep 103 (by omega)) hai.2⟩,
    stored_of_normFrame had (NormFrame.of_arithmetic htf),
    ready_of_signed_arithmetic har hb htr htf,
    blank_of_eq (keep 106 (by omega)) ha106, hframe⟩
  simp only [dotValues, Function.update_self,
    Function.update_of_ne (show (30 : ℕ) ≠ 31 by omega)] at hmcost
  dsimp only [normCost]
  omega

end Maxwell.Cost.RationalNormalize
