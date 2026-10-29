import Maxwell.Cost.CalibrationMatrix.Semantics
import Maxwell.Cost.CalibrationMatrix.MatrixState

namespace Maxwell.Cost.CalibrationMatrix

/-- Two disjoint vector buffers exchange their physical roles after a product. -/
structure Buffers (n : ℕ) where
  data : Data (n*n) n
  output : OutputLayout
  positive : Vector (List Bool) n
  negative : Vector (List Bool) n

def Buffers.advance {n : ℕ} (b : Buffers n) : Buffers n :=
  ⟨{b.data with
      vectorPositiveBase := b.output.positiveBase
      vectorNegativeBase := b.output.negativeBase
      vectorPositive := Vector.ofFn b.data.positivePayload
      vectorNegative := Vector.ofFn b.data.negativePayload},
    ⟨b.data.vectorPositiveBase, b.data.vectorNegativeBase⟩,
    b.data.vectorPositive, b.data.vectorNegative⟩

def Buffers.Sized {n : ℕ} (b : Buffers n) (B : ℕ) : Prop := b.data.Sized B ∧ b.output.Sized B

def Buffers.Fits {n : ℕ} (b : Buffers n) : Prop :=
  (∀ i, (b.data.outputPositive i).bits.length ≤ addressValue b.data.width) ∧
  (∀ i, (b.data.outputNegative i).bits.length ≤ addressValue b.data.width)

structure Buffers.Separated {n : ℕ} (b : Buffers n) : Prop where
  inputs : InputSeparated b.data b.output.positiveBase b.output.negativeBase n
  outputs : b.output.Separated n (addressValue b.data.width)
  vectors : IncidenceEncoding.Separated (addressValue b.data.vectorPositiveBase) (n*addressValue b.data.width)
    (addressValue b.data.vectorNegativeBase) (n*addressValue b.data.width)
  matrixPositive_vectorPositive : IncidenceEncoding.Separated (addressValue b.data.matrixPositiveBase)
    (n*n*addressValue b.data.width) (addressValue b.data.vectorPositiveBase) (n*addressValue b.data.width)
  matrixPositive_vectorNegative : IncidenceEncoding.Separated (addressValue b.data.matrixPositiveBase)
    (n*n*addressValue b.data.width) (addressValue b.data.vectorNegativeBase) (n*addressValue b.data.width)
  matrixNegative_vectorPositive : IncidenceEncoding.Separated (addressValue b.data.matrixNegativeBase)
    (n*n*addressValue b.data.width) (addressValue b.data.vectorPositiveBase) (n*addressValue b.data.width)
  matrixNegative_vectorNegative : IncidenceEncoding.Separated (addressValue b.data.matrixNegativeBase)
    (n*n*addressValue b.data.width) (addressValue b.data.vectorNegativeBase) (n*addressValue b.data.width)

theorem Buffers.Sized.advance {n B : ℕ} {b : Buffers n} (h : b.Sized B) : b.advance.Sized B := by
  rcases h with ⟨⟨hw, hW, hmp, hmn, hvp, hvn⟩, hop, hon⟩
  exact ⟨⟨hw, hW, hmp, hmn, hop, hon⟩, hvp, hvn⟩

theorem Buffers.Separated.advance {n : ℕ} {b : Buffers n} (h : b.Separated) : b.advance.Separated := by
  refine ⟨?_, h.vectors, h.outputs, h.inputs.matrixPositive_positive,
    h.inputs.matrixPositive_negative, h.inputs.matrixNegative_positive, h.inputs.matrixNegative_negative⟩
  exact ⟨h.matrixPositive_vectorPositive, h.matrixPositive_vectorNegative,
    h.matrixNegative_vectorPositive, h.matrixNegative_vectorNegative,
    h.inputs.vectorPositive_positive.symm, h.inputs.vectorNegative_positive.symm,
    h.inputs.vectorPositive_negative.symm, h.inputs.vectorNegative_negative.symm⟩

theorem Buffers.advance_decodes {n : ℕ} {b : Buffers n} {A : ChannelMatrix n} {x : Channels n}
    (h : b.data.Decodes A x) (hfit : b.Fits) : b.advance.data.Decodes A (matvec A x) := by
  refine ⟨h.matrixPositive, h.matrixNegative, ?_, ?_⟩
  · intro j
    change addressValue ((Vector.ofFn b.data.positivePayload).get j) = _
    rw [b.data.positivePayload_eq_matvec h]
    exact channelWords_value _ _ j (by simpa only [b.data.outputPositive_eq_matvec h j] using hfit.1 j)
  · intro j
    change addressValue ((Vector.ofFn b.data.negativePayload).get j) = _
    rw [b.data.negativePayload_eq_matvec h]
    exact channelWords_value _ _ j (by simpa only [b.data.outputNegative_eq_matvec h j] using hfit.2 j)

def Buffers.iterate {n : ℕ} (b : Buffers n) : ℕ → Buffers n
  | 0 => b
  | k+1 => (b.iterate k).advance

@[simp] theorem Buffers.iterate_width {n : ℕ} (b : Buffers n) (k : ℕ) :
    (b.iterate k).data.width = b.data.width := by induction k <;> simp_all [Buffers.iterate, Buffers.advance]

theorem Buffers.Sized.iterate {n B : ℕ} {b : Buffers n} (h : b.Sized B) (k : ℕ) : (b.iterate k).Sized B := by
  induction k with
  | zero => exact h
  | succ k ih => exact ih.advance

theorem Buffers.Separated.iterate {n : ℕ} {b : Buffers n} (h : b.Separated) (k : ℕ) : (b.iterate k).Separated := by
  induction k with
  | zero => exact h
  | succ k ih => exact ih.advance

end Maxwell.Cost.CalibrationMatrix
