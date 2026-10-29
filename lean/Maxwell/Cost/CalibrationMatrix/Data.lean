import Maxwell.Cost.CalibrationMatrix.ReadOperand

namespace Maxwell.Cost.CalibrationMatrix

/-- Four concrete fixed-width memory arrays and their persistent layout words.
The matrix index and vector index are separate live counters on tapes102/103. -/
structure Data (m n : ℕ) where
  width : List Bool
  clock : List Bool
  matrixPositiveBase : List Bool
  matrixNegativeBase : List Bool
  vectorPositiveBase : List Bool
  vectorNegativeBase : List Bool
  matrixPositive : Vector (List Bool) m
  matrixNegative : Vector (List Bool) m
  vectorPositive : Vector (List Bool) n
  vectorNegative : Vector (List Bool) n
  width_nonempty : 0 < width.length
  clock_length : clock.length = addressValue width

structure Stored {m n : ℕ} (d : Data m n) (s : BitRAMState) : Prop where
  width : BankArray.Word s 100 d.width
  clock : BankArray.Word s 101 d.clock
  matrixPositiveBase : BankArray.Word s 110 d.matrixPositiveBase
  matrixNegativeBase : BankArray.Word s 111 d.matrixNegativeBase
  vectorPositiveBase : BankArray.Word s 112 d.vectorPositiveBase
  vectorNegativeBase : BankArray.Word s 113 d.vectorNegativeBase
  matrixPositive : BitArray.Represents s.memory (addressValue d.matrixPositiveBase)
    (addressValue d.width) d.matrixPositive
  matrixNegative : BitArray.Represents s.memory (addressValue d.matrixNegativeBase)
    (addressValue d.width) d.matrixNegative
  vectorPositive : BitArray.Represents s.memory (addressValue d.vectorPositiveBase)
    (addressValue d.width) d.vectorPositive
  vectorNegative : BitArray.Represents s.memory (addressValue d.vectorNegativeBase)
    (addressValue d.width) d.vectorNegative

theorem Stored.of_frame {m n : ℕ} {d : Data m n} {s t : BitRAMState}
    (h : Stored d s) (hf : StepFrame s t) : Stored d t := by
  have keep (i : ℕ) (hi : 100 ≤ i) : t.tapes i = s.tapes i :=
    hf.2.2.2.2.1 i (Or.inr (by omega)) (Or.inr (by omega))
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

def Indices (s : BitRAMState) (matrixIndex vectorIndex : List Bool) : Prop :=
  BankArray.Word s 102 matrixIndex ∧ BankArray.Word s 103 vectorIndex

theorem Indices.of_frame {s t : BitRAMState} {mi vi : List Bool}
    (h : Indices s mi vi) (hf : StepFrame s t) : Indices t mi vi :=
  ⟨BankArray.word_of_eq (hf.2.2.2.2.1 102 (Or.inr (by omega)) (Or.inr (by omega))) h.1,
    BankArray.word_of_eq (hf.2.2.2.2.1 103 (Or.inr (by omega)) (Or.inr (by omega))) h.2⟩

def Data.positiveTerm {m n : ℕ} (d : Data m n) (i : Fin m) (j : Fin n) : ℕ :=
  addressValue (d.matrixPositive.get i)*addressValue (d.vectorPositive.get j) +
    addressValue (d.matrixNegative.get i)*addressValue (d.vectorNegative.get j)

def Data.negativeTerm {m n : ℕ} (d : Data m n) (i : Fin m) (j : Fin n) : ℕ :=
  addressValue (d.matrixPositive.get i)*addressValue (d.vectorNegative.get j) +
    addressValue (d.matrixNegative.get i)*addressValue (d.vectorPositive.get j)

end Maxwell.Cost.CalibrationMatrix
