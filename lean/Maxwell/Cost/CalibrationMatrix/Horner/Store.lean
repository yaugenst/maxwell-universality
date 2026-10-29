import Maxwell.Cost.CalibrationMatrix.PowerSemantics
import Maxwell.Cost.CalibrationMatrix.Affine.Data

namespace Maxwell.Cost.CalibrationMatrix.Horner
open Structured

/-- Persistent descriptors for w,x,u,new-w,new-x,t, in signed pairs.
The matvec descriptors112..115 are expendable copies of these words. -/
def baseBank (i : Fin 12) : ℕ :=
  if i.val < 6 then 120+i.val else if i.val < 8 then 122+i.val
    else if i.val < 10 then 124+i.val else 120+i.val

theorem baseBank_bounds (i : Fin 12) : 120 ≤ baseBank i ∧ baseBank i ≤ 133 := by
  unfold baseBank
  split_ifs <;> omega

structure Data (n : ℕ) where
  width : List Bool
  clock : List Bool
  matrixPositiveBase : List Bool
  matrixNegativeBase : List Bool
  matrixPositive : Vector (List Bool) (n*n)
  matrixNegative : Vector (List Bool) (n*n)
  bases : Fin 12 → List Bool
  K : ℕ
  S : ℕ
  width_nonempty : 0 < width.length
  width_positive : 0 < addressValue width
  clock_length : clock.length = addressValue width
  separated : ∀ i j, i ≠ j → IncidenceEncoding.Separated
    (addressValue (bases i)) (n*addressValue width) (addressValue (bases j)) (n*addressValue width)
  matrixPositive_separated : ∀ i, IncidenceEncoding.Separated
    (addressValue matrixPositiveBase) (n*n*addressValue width) (addressValue (bases i)) (n*addressValue width)
  matrixNegative_separated : ∀ i, IncidenceEncoding.Separated
    (addressValue matrixNegativeBase) (n*n*addressValue width) (addressValue (bases i)) (n*addressValue width)

structure Stored {n : ℕ} (d : Data n) (words : Fin 12 → Vector (List Bool) n) (s : BitRAMState) : Prop where
  width : BankArray.Word s 100 d.width
  clock : BankArray.Word s 101 d.clock
  matrixPositiveBase : BankArray.Word s 110 d.matrixPositiveBase
  matrixNegativeBase : BankArray.Word s 111 d.matrixNegativeBase
  bases : ∀ i, BankArray.Word s (baseBank i) (d.bases i)
  K : RationalAccumulator.Word s 126 d.K
  S : RationalAccumulator.Word s 127 d.S
  matrixPositive : BitArray.Represents s.memory (addressValue d.matrixPositiveBase) (addressValue d.width) d.matrixPositive
  matrixNegative : BitArray.Represents s.memory (addressValue d.matrixNegativeBase) (addressValue d.width) d.matrixNegative
  arrays : ∀ i, BitArray.Represents s.memory (addressValue (d.bases i)) (addressValue d.width) (words i)

def Data.Sized {n : ℕ} (d : Data n) (B : ℕ) : Prop :=
  d.width.length ≤ B ∧ addressValue d.width ≤ B ∧ d.matrixPositiveBase.length ≤ B ∧
    d.matrixNegativeBase.length ≤ B ∧ (∀ i, (d.bases i).length ≤ B) ∧ d.K.bits.length ≤ B ∧ d.S.bits.length ≤ B

def Metadata (i : ℕ) : Prop := i = 100 ∨ i = 101 ∨ i = 110 ∨ i = 111 ∨ (120 ≤ i ∧ i ≤ 133)

theorem Stored.of_memory_tapes {n : ℕ} {d : Data n} {words : Fin 12 → Vector (List Bool) n}
    {s t : BitRAMState} (h : Stored d words s) (hm : t.memory = s.memory)
    (keep : ∀ i, Metadata i → t.tapes i = s.tapes i) : Stored d words t :=
  ⟨BankArray.word_of_eq (keep 100 (by simp [Metadata])) h.width,
    BankArray.word_of_eq (keep 101 (by simp [Metadata])) h.clock,
    BankArray.word_of_eq (keep 110 (by simp [Metadata])) h.matrixPositiveBase,
    BankArray.word_of_eq (keep 111 (by simp [Metadata])) h.matrixNegativeBase,
    fun i => BankArray.word_of_eq (keep _ (by right; right; right; right; exact baseBank_bounds i)) (h.bases i),
    RationalAccumulator.word_of_eq (keep 126 (by simp [Metadata])) h.K,
    RationalAccumulator.word_of_eq (keep 127 (by simp [Metadata])) h.S,
    by simpa only [hm] using h.matrixPositive, by simpa only [hm] using h.matrixNegative,
    fun i => by simpa only [hm] using h.arrays i⟩

theorem PowerFrame.metadata {s t : BitRAMState} (h : CalibrationMatrix.PowerFrame s t)
    (i : ℕ) (hi : Metadata i) : t.tapes i = s.tapes i := by
  rcases hi with hi | hi | hi | hi | ⟨hi, hi'⟩ <;>
    apply h.2.2.2.1 i <;> omega

/-- Every represented bit lies outside a disjoint output pair. -/
theorem represents_of_output {m rows width base : ℕ} {values : Vector (List Bool) m}
    {l : OutputLayout} {s t : BitRAMState}
    (h : BitArray.Represents s.memory base width values) (hm : OutputOutside l rows width s t)
    (hp : IncidenceEncoding.Separated base (m*width) (addressValue l.positiveBase) (rows*width))
    (hn : IncidenceEncoding.Separated base (m*width) (addressValue l.negativeBase) (rows*width)) :
    BitArray.Represents t.memory base width values := by
  refine ⟨h.length, ?_⟩
  intro i j hj
  rw [hm]
  · exact h.bits i j hj
  · have hs := Nat.mul_le_mul_right width (show i.val+1 ≤ m by omega)
    rcases hp with hp | hp
    · left; nlinarith
    · right; omega
  · have hs := Nat.mul_le_mul_right width (show i.val+1 ≤ m by omega)
    rcases hn with hn | hn
    · left; nlinarith
    · right; omega

def setOutputs {n : ℕ} (words : Fin 12 → Vector (List Bool) n)
    (p q : Fin 12) (positive negative : Vector (List Bool) n) : Fin 12 → Vector (List Bool) n :=
  Function.update (Function.update words p positive) q negative

theorem Stored.after_output {n : ℕ} {d : Data n} {words : Fin 12 → Vector (List Bool) n}
    {s t : BitRAMState} (h : Stored d words s) (p q : Fin 12) (hpq : p ≠ q)
    (positive negative : Vector (List Bool) n)
    (hf : CalibrationMatrix.PowerFrame s t)
    (hm : OutputOutside ⟨d.bases p,d.bases q⟩ n (addressValue d.width) s t)
    (hp : BitArray.Represents t.memory (addressValue (d.bases p)) (addressValue d.width) positive)
    (hn : BitArray.Represents t.memory (addressValue (d.bases q)) (addressValue d.width) negative) :
    Stored d (setOutputs words p q positive negative) t := by
  have keep := PowerFrame.metadata hf
  refine ⟨BankArray.word_of_eq (keep 100 (by simp [Metadata])) h.width,
    BankArray.word_of_eq (keep 101 (by simp [Metadata])) h.clock,
    BankArray.word_of_eq (keep 110 (by simp [Metadata])) h.matrixPositiveBase,
    BankArray.word_of_eq (keep 111 (by simp [Metadata])) h.matrixNegativeBase,
    fun i => BankArray.word_of_eq (keep _ (by right; right; right; right; exact baseBank_bounds i)) (h.bases i),
    RationalAccumulator.word_of_eq (keep 126 (by simp [Metadata])) h.K,
    RationalAccumulator.word_of_eq (keep 127 (by simp [Metadata])) h.S,
    represents_of_output h.matrixPositive hm (d.matrixPositive_separated p) (d.matrixPositive_separated q),
    represents_of_output h.matrixNegative hm (d.matrixNegative_separated p) (d.matrixNegative_separated q), ?_⟩
  intro i
  by_cases hiq : i = q
  · subst i; simpa only [setOutputs, Function.update_self] using hn
  · by_cases hip : i = p
    · subst i; simpa only [setOutputs, Function.update_of_ne hpq, Function.update_self] using hp
    · simp only [setOutputs, Function.update_of_ne hiq, Function.update_of_ne hip]
      exact represents_of_output (h.arrays i) hm (d.separated i p hip) (d.separated i q hiq)

end Maxwell.Cost.CalibrationMatrix.Horner
