import Maxwell.Cost.CalibrationMatrix.Row
import Maxwell.Cost.CalibrationMatrix.Value

namespace Maxwell.Cost.CalibrationMatrix
open scoped BigOperators

/-- Row-major slot of the concrete dense matrix arrays. -/
def matrixSlot {n : ℕ} (i j : Fin n) : Fin (n*n) := rowIndex (i.val*n) (row_bound i) j

/-- The decoded channels are the actual values of the supplied memory words. -/
structure Data.Decodes {n : ℕ} (d : Data (n*n) n) (A : ChannelMatrix n) (x : Channels n) : Prop where
  matrixPositive : ∀ i j, addressValue (d.matrixPositive.get (matrixSlot i j)) = A.positive i j
  matrixNegative : ∀ i j, addressValue (d.matrixNegative.get (matrixSlot i j)) = A.negative i j
  vectorPositive : ∀ j, addressValue (d.vectorPositive.get j) = x.positive j
  vectorNegative : ∀ j, addressValue (d.vectorNegative.get j) = x.negative j

theorem Data.outputPositive_eq_matvec {n : ℕ} {d : Data (n*n) n}
    {A : ChannelMatrix n} {x : Channels n} (h : d.Decodes A x) (i : Fin n) :
    d.outputPositive i = (matvec A x).positive i := by
  apply Finset.sum_congr rfl
  intro j _
  change addressValue (d.matrixPositive.get (matrixSlot i j))*addressValue (d.vectorPositive.get j) +
    addressValue (d.matrixNegative.get (matrixSlot i j))*addressValue (d.vectorNegative.get j) = _
  rw [h.matrixPositive, h.matrixNegative, h.vectorPositive, h.vectorNegative]

theorem Data.outputNegative_eq_matvec {n : ℕ} {d : Data (n*n) n}
    {A : ChannelMatrix n} {x : Channels n} (h : d.Decodes A x) (i : Fin n) :
    d.outputNegative i = (matvec A x).negative i := by
  apply Finset.sum_congr rfl
  intro j _
  change addressValue (d.matrixPositive.get (matrixSlot i j))*addressValue (d.vectorNegative.get j) +
    addressValue (d.matrixNegative.get (matrixSlot i j))*addressValue (d.vectorPositive.get j) = _
  rw [h.matrixPositive, h.matrixNegative, h.vectorPositive, h.vectorNegative]

def channelWords {n : ℕ} (width : ℕ) (values : Fin n → ℕ) : Vector (List Bool) n :=
  Vector.ofFn fun i => FixedWidth.bits width (values i).bits

@[simp] theorem channelWords_get {n : ℕ} (width : ℕ) (values : Fin n → ℕ) (i : Fin n) :
    (channelWords width values).get i = FixedWidth.bits width (values i).bits := by
  simp [channelWords, Vector.get, Fin.cast]

theorem channelWords_value {n : ℕ} (width : ℕ) (values : Fin n → ℕ) (i : Fin n)
    (h : (values i).bits.length ≤ width) :
    addressValue ((channelWords width values).get i) = values i := by
  rw [channelWords_get, FixedWidth.bits_value _ _ h, addressValue_bits]

theorem Data.positivePayload_eq_matvec {n : ℕ} {d : Data (n*n) n}
    {A : ChannelMatrix n} {x : Channels n} (h : d.Decodes A x) :
    Vector.ofFn d.positivePayload = channelWords (addressValue d.width) (matvec A x).positive := by
  congr 1
  funext i
  simp only [Data.positivePayload, d.outputPositive_eq_matvec h i]

theorem Data.negativePayload_eq_matvec {n : ℕ} {d : Data (n*n) n}
    {A : ChannelMatrix n} {x : Channels n} (h : d.Decodes A x) :
    Vector.ofFn d.negativePayload = channelWords (addressValue d.width) (matvec A x).negative := by
  congr 1
  funext i
  simp only [Data.negativePayload, d.outputNegative_eq_matvec h i]

end Maxwell.Cost.CalibrationMatrix
