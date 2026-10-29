import Maxwell.Cost.CalibrationMatrix.Data
import Maxwell.Cost.CalibrationMatrix.WriteRow

/-! The actual two output-array writes preserve all four input arrays and
the persistent words needed by the next matrix row. -/
namespace Maxwell.Cost.CalibrationMatrix

structure InputSeparated {m n : ℕ} (d : Data m n)
    (outPosBase outNegBase : List Bool) (rows : ℕ) : Prop where
  matrixPositive_positive : IncidenceEncoding.Separated (addressValue d.matrixPositiveBase)
    (m * addressValue d.width) (addressValue outPosBase) (rows * addressValue d.width)
  matrixPositive_negative : IncidenceEncoding.Separated (addressValue d.matrixPositiveBase)
    (m * addressValue d.width) (addressValue outNegBase) (rows * addressValue d.width)
  matrixNegative_positive : IncidenceEncoding.Separated (addressValue d.matrixNegativeBase)
    (m * addressValue d.width) (addressValue outPosBase) (rows * addressValue d.width)
  matrixNegative_negative : IncidenceEncoding.Separated (addressValue d.matrixNegativeBase)
    (m * addressValue d.width) (addressValue outNegBase) (rows * addressValue d.width)
  vectorPositive_positive : IncidenceEncoding.Separated (addressValue d.vectorPositiveBase)
    (n * addressValue d.width) (addressValue outPosBase) (rows * addressValue d.width)
  vectorPositive_negative : IncidenceEncoding.Separated (addressValue d.vectorPositiveBase)
    (n * addressValue d.width) (addressValue outNegBase) (rows * addressValue d.width)
  vectorNegative_positive : IncidenceEncoding.Separated (addressValue d.vectorNegativeBase)
    (n * addressValue d.width) (addressValue outPosBase) (rows * addressValue d.width)
  vectorNegative_negative : IncidenceEncoding.Separated (addressValue d.vectorNegativeBase)
    (n * addressValue d.width) (addressValue outNegBase) (rows * addressValue d.width)

theorem Stored.after_row_write {m n rows : ℕ} {d : Data m n} {s t : BitRAMState}
    (h : Stored d s) (outPosBase outNegBase : List Bool) (row : Fin rows)
    (positivePayload negativePayload : List Bool)
    (hp : positivePayload.length = addressValue d.width)
    (hn : negativePayload.length = addressValue d.width)
    (hsep : InputSeparated d outPosBase outNegBase rows)
    (hf : RowFrame s t)
    (hm : t.memory = MemoryWord.writeBits
      (MemoryWord.writeBits s.memory
        (addressValue outPosBase + row.val * addressValue d.width) positivePayload)
      (addressValue outNegBase + row.val * addressValue d.width) negativePayload) : Stored d t := by
  have keep (i : ℕ) (hi : 100 ≤ i) : t.tapes i = s.tapes i :=
    hf.2.2.2.1 i (Or.inr (by omega)) (by omega) (by omega) (by omega)
  have preserve {k base : ℕ} {words : Vector (List Bool) k}
      (ha : BitArray.Represents s.memory base (addressValue d.width) words)
      (hpos : IncidenceEncoding.Separated base (k * addressValue d.width)
        (addressValue outPosBase) (rows * addressValue d.width))
      (hneg : IncidenceEncoding.Separated base (k * addressValue d.width)
        (addressValue outNegBase) (rows * addressValue d.width)) :
      BitArray.Represents t.memory base (addressValue d.width) words := by
    rw [hm]
    exact IncidenceEncoding.represents_write_disjoint
      (IncidenceEncoding.represents_write_disjoint ha _ _ row positivePayload hp hpos)
      _ _ row negativePayload hn hneg
  exact ⟨BankArray.word_of_eq (keep 100 (by omega)) h.width,
    BankArray.word_of_eq (keep 101 (by omega)) h.clock,
    BankArray.word_of_eq (keep 110 (by omega)) h.matrixPositiveBase,
    BankArray.word_of_eq (keep 111 (by omega)) h.matrixNegativeBase,
    BankArray.word_of_eq (keep 112 (by omega)) h.vectorPositiveBase,
    BankArray.word_of_eq (keep 113 (by omega)) h.vectorNegativeBase,
    preserve h.matrixPositive hsep.matrixPositive_positive hsep.matrixPositive_negative,
    preserve h.matrixNegative hsep.matrixNegative_positive hsep.matrixNegative_negative,
    preserve h.vectorPositive hsep.vectorPositive_positive hsep.vectorPositive_negative,
    preserve h.vectorNegative hsep.vectorNegative_positive hsep.vectorNegative_negative⟩

end Maxwell.Cost.CalibrationMatrix
