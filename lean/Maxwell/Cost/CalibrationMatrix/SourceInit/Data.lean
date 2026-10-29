import Maxwell.Cost.CalibrationMatrix.SourceInit.Values
import Maxwell.Cost.CalibrationMatrix.Affine.Data

namespace Maxwell.Cost.CalibrationMatrix.SourceInit

def inputBaseBank (i : Fin 3) : ℕ := 160+i.val
def outputBaseBank (i : Fin 4) : ℕ := 120+i.val

/-- Three actual sparse input arrays and four disjoint dense output arrays.
The source records contain an in-range radix index and two natural channels. -/
structure Data (m n : ℕ) where
  width : List Bool
  clock : List Bool
  dimension : List Bool
  count : List Bool
  inputBases : Fin 3 → List Bool
  outputBases : Fin 4 → List Bool
  inputWords : Fin 3 → Vector (List Bool) m
  width_nonempty : 0 < width.length
  width_positive : 0 < addressValue width
  clock_length : clock.length = addressValue width
  dimension_value : addressValue dimension = n
  count_value : addressValue count = m
  index_bound : ∀ j : Fin m, addressValue ((inputWords 0).get j) < n
  output_separated : ∀ i j, i ≠ j → IncidenceEncoding.Separated
    (addressValue (outputBases i)) (n*addressValue width)
    (addressValue (outputBases j)) (n*addressValue width)
  input_separated : ∀ i j, IncidenceEncoding.Separated
    (addressValue (inputBases i)) (m*addressValue width)
    (addressValue (outputBases j)) (n*addressValue width)

def Data.records {m n : ℕ} (d : Data m n) : Records m n where
  index j := ⟨addressValue ((d.inputWords 0).get j), d.index_bound j⟩
  positive j := addressValue ((d.inputWords 1).get j)
  negative j := addressValue ((d.inputWords 2).get j)

def Data.Sized {m n : ℕ} (d : Data m n) (B : ℕ) : Prop :=
  d.width.length ≤ B ∧ addressValue d.width ≤ B ∧
  d.dimension.length ≤ B ∧ d.count.length ≤ B ∧
  (∀ i, (d.inputBases i).length ≤ B) ∧ ∀ i, (d.outputBases i).length ≤ B

structure Stored {m n : ℕ} (d : Data m n) (words : Fin 4 → Vector (List Bool) n)
    (s : BitRAMState) : Prop where
  width : BankArray.Word s 100 d.width
  clock : BankArray.Word s 101 d.clock
  dimension : BankArray.Word s 107 d.dimension
  count : BankArray.Word s 159 d.count
  inputBases : ∀ i, BankArray.Word s (inputBaseBank i) (d.inputBases i)
  outputBases : ∀ i, BankArray.Word s (outputBaseBank i) (d.outputBases i)
  inputs : ∀ i, BitArray.Represents s.memory (addressValue (d.inputBases i))
    (addressValue d.width) (d.inputWords i)
  outputs : ∀ i, BitArray.Represents s.memory (addressValue (d.outputBases i))
    (addressValue d.width) (words i)

theorem Stored.of_tapes_memory {m n : ℕ} {d : Data m n}
    {words : Fin 4 → Vector (List Bool) n} {s t : BitRAMState} (h : Stored d words s)
    (hm : t.memory = s.memory)
    (ht : ∀ i, i = 100 ∨ i = 101 ∨ i = 107 ∨ 120 ≤ i → t.tapes i = s.tapes i) :
    Stored d words t :=
  ⟨BankArray.word_of_eq (ht 100 (by omega)) h.width,
    BankArray.word_of_eq (ht 101 (by omega)) h.clock,
    BankArray.word_of_eq (ht 107 (by omega)) h.dimension,
    BankArray.word_of_eq (ht 159 (by omega)) h.count,
    fun i => BankArray.word_of_eq (ht _ (by simp only [inputBaseBank]; omega)) (h.inputBases i),
    fun i => BankArray.word_of_eq (ht _ (by simp only [outputBaseBank]; omega)) (h.outputBases i),
    fun i => by simpa only [hm] using h.inputs i,
    fun i => by simpa only [hm] using h.outputs i⟩

theorem Stored.of_step {m n : ℕ} {d : Data m n}
    {words : Fin 4 → Vector (List Bool) n} {s t : BitRAMState}
    (h : Stored d words s) (hf : StepFrame s t) : Stored d words t :=
  h.of_tapes_memory hf.1 (fun i hi => hf.2.2.2.2.1 i (Or.inr (by omega)) (Or.inr (by omega)))

def setPair {n : ℕ} (words : Fin 4 → Vector (List Bool) n) (a b : Fin 4)
    (row : Fin n) (positive negative : List Bool) : Fin 4 → Vector (List Bool) n :=
  Function.update (Function.update words a ((words a).set row positive)) b ((words b).set row negative)

theorem Stored.after_pair {m n : ℕ} {d : Data m n}
    {words : Fin 4 → Vector (List Bool) n} {s t : BitRAMState}
    (h : Stored d words s) (a b : Fin 4) (hab : a ≠ b)
    (row : Fin n) (positive negative : List Bool)
    (hp : positive.length = addressValue d.width) (hn : negative.length = addressValue d.width)
    (hf : RowFrame s t)
    (hm : t.memory = MemoryWord.writeBits
      (MemoryWord.writeBits s.memory (addressValue (d.outputBases a)+row.val*addressValue d.width) positive)
      (addressValue (d.outputBases b)+row.val*addressValue d.width) negative)
    (hpa : BitArray.Represents t.memory (addressValue (d.outputBases a)) (addressValue d.width)
      ((words a).set row positive))
    (hna : BitArray.Represents t.memory (addressValue (d.outputBases b)) (addressValue d.width)
      ((words b).set row negative)) : Stored d (setPair words a b row positive negative) t := by
  have keep (i : ℕ) (hi : 100 ≤ i) : t.tapes i = s.tapes i :=
    hf.2.2.2.1 i (Or.inr (by omega)) (by omega) (by omega) (by omega)
  refine ⟨BankArray.word_of_eq (keep 100 (by omega)) h.width,
    BankArray.word_of_eq (keep 101 (by omega)) h.clock,
    BankArray.word_of_eq (keep 107 (by omega)) h.dimension,
    BankArray.word_of_eq (keep 159 (by omega)) h.count,
    fun i => BankArray.word_of_eq (keep _ (by simp only [inputBaseBank]; omega)) (h.inputBases i),
    fun i => BankArray.word_of_eq (keep _ (by simp only [outputBaseBank]; omega)) (h.outputBases i), ?_, ?_⟩
  · intro i
    rw [hm]
    exact IncidenceEncoding.represents_write_disjoint
      (IncidenceEncoding.represents_write_disjoint (h.inputs i) _ _ row positive hp (d.input_separated i a))
      _ _ row negative hn (d.input_separated i b)
  · intro i
    by_cases hib : i = b
    · subst i; simpa only [setPair, Function.update_self] using hna
    · by_cases hia : i = a
      · subst i; simpa only [setPair, Function.update_of_ne hab, Function.update_self] using hpa
      · simp only [setPair, Function.update_of_ne hib, Function.update_of_ne hia]
        rw [hm]
        exact IncidenceEncoding.represents_write_disjoint
          (IncidenceEncoding.represents_write_disjoint (h.outputs i) _ _ row positive hp
            (d.output_separated i a hia)) _ _ row negative hn (d.output_separated i b hib)

/-- Outside the four output intervals, source initialization preserves
memory pointwise, including any separately allocated matrix arrays. -/
def Outside {m n : ℕ} (d : Data m n) (s t : BitRAMState) : Prop :=
  ∀ address, (∀ port : Fin 4,
    address < addressValue (d.outputBases port) ∨
      addressValue (d.outputBases port)+n*addressValue d.width ≤ address) →
    t.memory address = s.memory address

theorem Outside.refl {m n : ℕ} (d : Data m n) (s : BitRAMState) : Outside d s s := fun _ _ => rfl

theorem Outside.trans {m n : ℕ} {d : Data m n} {s t u : BitRAMState}
    (h : Outside d s t) (k : Outside d t u) : Outside d s u :=
  fun a ha => (k a ha).trans (h a ha)

theorem Outside.of_memory {m n : ℕ} {d : Data m n} {s t : BitRAMState}
    (h : t.memory = s.memory) : Outside d s t := by intro a _; rw [h]

theorem Outside.of_pair {m n : ℕ} {d : Data m n} {s t : BitRAMState}
    (a b : Fin 4) (row : Fin n) (positive negative : List Bool)
    (hp : positive.length = addressValue d.width) (hn : negative.length = addressValue d.width)
    (hm : t.memory = MemoryWord.writeBits
      (MemoryWord.writeBits s.memory (addressValue (d.outputBases a)+row.val*addressValue d.width) positive)
      (addressValue (d.outputBases b)+row.val*addressValue d.width) negative) : Outside d s t := by
  intro address ha
  have hslot := Nat.mul_le_mul_right (addressValue d.width) (show row.val+1 ≤ n by omega)
  have outside (port : Fin 4) (bits : List Bool) (hlen : bits.length = addressValue d.width) :
      address < addressValue (d.outputBases port)+row.val*addressValue d.width ∨
        addressValue (d.outputBases port)+row.val*addressValue d.width+bits.length ≤ address := by
    rw [hlen]
    rcases ha port with h | h
    · left; omega
    · right; nlinarith
  rw [hm, MemoryWord.writeBits_outside _ _ _ _ (outside b negative hn),
    MemoryWord.writeBits_outside _ _ _ _ (outside a positive hp)]

end Maxwell.Cost.CalibrationMatrix.SourceInit
