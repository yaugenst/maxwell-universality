import Maxwell.Cost.CalibrationMatrix.Affine.Write
import Maxwell.Cost.CalibrationMatrix.Rows

namespace Maxwell.Cost.CalibrationMatrix.Affine
open Structured

/-- Six input channels followed by the two scaled-source and two Horner
output channels. Each pair has its own disjoint fixed-width array. -/
def baseBank (i : Fin 10) : ℕ :=
  if i.val < 6 then 120+i.val else if i.val < 8 then 122+i.val else 106+i.val

theorem baseBank_ge (i : Fin 10) : 110 ≤ baseBank i := by
  unfold baseBank
  split_ifs <;> omega

structure Data (n : ℕ) where
  width : List Bool
  clock : List Bool
  bases : Fin 10 → List Bool
  K : ℕ
  S : ℕ
  width_nonempty : 0 < width.length
  width_positive : 0 < addressValue width
  clock_length : clock.length = addressValue width
  separated : ∀ i j, i ≠ j → IncidenceEncoding.Separated
    (addressValue (bases i)) (n*addressValue width) (addressValue (bases j)) (n*addressValue width)

structure Stored {n : ℕ} (d : Data n) (words : Fin 10 → Vector (List Bool) n)
    (s : BitRAMState) : Prop where
  width : BankArray.Word s 100 d.width
  clock : BankArray.Word s 101 d.clock
  bases : ∀ i, BankArray.Word s (baseBank i) (d.bases i)
  K : RationalAccumulator.Word s 126 d.K
  S : RationalAccumulator.Word s 127 d.S
  arrays : ∀ i, BitArray.Represents s.memory (addressValue (d.bases i)) (addressValue d.width) (words i)

def Data.Sized {n : ℕ} (d : Data n) (B : ℕ) : Prop :=
  d.width.length ≤ B ∧ addressValue d.width ≤ B ∧
    (∀ i, (d.bases i).length ≤ B) ∧ d.K.bits.length ≤ B ∧ d.S.bits.length ≤ B

theorem Stored.of_step {n : ℕ} {d : Data n} {words : Fin 10 → Vector (List Bool) n}
    {s t : BitRAMState} (h : Stored d words s) (hf : StepFrame s t) : Stored d words t :=
  ⟨frame_word hf 100 (by omega) h.width, frame_word hf 101 (by omega) h.clock,
    fun i => frame_word hf _ (by have := baseBank_ge i; omega) (h.bases i),
    frame_number hf 126 (by omega) h.K, frame_number hf 127 (by omega) h.S,
    fun i => by simpa only [hf.1] using h.arrays i⟩

def setPair {n : ℕ} (words : Fin 10 → Vector (List Bool) n) (a b : Fin 10)
    (row : Fin n) (positive negative : List Bool) : Fin 10 → Vector (List Bool) n :=
  Function.update (Function.update words a ((words a).set row positive)) b ((words b).set row negative)

theorem Stored.after_pair {n : ℕ} {d : Data n} {words : Fin 10 → Vector (List Bool) n}
    {s t : BitRAMState} (h : Stored d words s) (a b : Fin 10) (hab : a ≠ b)
    (row : Fin n) (positive negative : List Bool)
    (hp : positive.length = addressValue d.width) (hn : negative.length = addressValue d.width)
    (hf : RowFrame s t)
    (hm : t.memory = MemoryWord.writeBits
      (MemoryWord.writeBits s.memory (addressValue (d.bases a)+row.val*addressValue d.width) positive)
      (addressValue (d.bases b)+row.val*addressValue d.width) negative)
    (hpa : BitArray.Represents t.memory (addressValue (d.bases a)) (addressValue d.width)
      ((words a).set row positive))
    (hna : BitArray.Represents t.memory (addressValue (d.bases b)) (addressValue d.width)
      ((words b).set row negative)) : Stored d (setPair words a b row positive negative) t := by
  have keep (i : ℕ) (hi : 100 ≤ i) : t.tapes i = s.tapes i :=
    hf.2.2.2.1 i (Or.inr (by omega)) (by omega) (by omega) (by omega)
  refine ⟨BankArray.word_of_eq (keep 100 (by omega)) h.width,
    BankArray.word_of_eq (keep 101 (by omega)) h.clock,
    fun i => BankArray.word_of_eq (keep _ (by have := baseBank_ge i; omega)) (h.bases i),
    RationalAccumulator.word_of_eq (keep 126 (by omega)) h.K,
    RationalAccumulator.word_of_eq (keep 127 (by omega)) h.S, ?_⟩
  intro i
  by_cases hib : i = b
  · subst i; simpa only [setPair, Function.update_self] using hna
  · by_cases hia : i = a
    · subst i; simpa only [setPair, Function.update_of_ne hab, Function.update_self] using hpa
    · simp only [setPair, Function.update_of_ne hib, Function.update_of_ne hia]
      rw [hm]
      exact IncidenceEncoding.represents_write_disjoint
        (IncidenceEncoding.represents_write_disjoint (h.arrays i) _ _ row positive hp (d.separated i a hia))
        _ _ row negative hn (d.separated i b hib)

theorem Stored.of_tapes_memory {n : ℕ} {d : Data n} {words : Fin 10 → Vector (List Bool) n}
    {s t : BitRAMState} (h : Stored d words s)
    (hm : t.memory = s.memory)
    (ht : ∀ i, i = 100 ∨ i = 101 ∨ 110 ≤ i → t.tapes i = s.tapes i) : Stored d words t :=
  ⟨BankArray.word_of_eq (ht 100 (by omega)) h.width,
    BankArray.word_of_eq (ht 101 (by omega)) h.clock,
    fun i => BankArray.word_of_eq (ht _ (Or.inr (Or.inr (baseBank_ge i)))) (h.bases i),
    RationalAccumulator.word_of_eq (ht 126 (by omega)) h.K,
    RationalAccumulator.word_of_eq (ht 127 (by omega)) h.S,
    fun i => by simpa only [hm] using h.arrays i⟩

end Maxwell.Cost.CalibrationMatrix.Affine
