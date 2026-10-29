import Maxwell.Cost.CalibrationMatrix.GenerationReady
import Maxwell.Cost.CalibrationMatrix.Semantics

namespace Maxwell.Cost.CalibrationMatrix.Generation
open Maxwell.Defect.FiniteStencil Maxwell.Spectral.Lattice

def row (R : ℕ) (k : Fin ((3*cubeWidth R^3)^2)) : Fin (3*cubeWidth R^3) :=
  ⟨k.val/(3*cubeWidth R^3), (Nat.div_lt_iff_lt_mul (by unfold cubeWidth; positivity)).2
    (by simpa only [pow_two] using k.isLt)⟩

def column (R : ℕ) (k : Fin ((3*cubeWidth R^3)^2)) : Fin (3*cubeWidth R^3) :=
  ⟨k.val%(3*cubeWidth R^3), Nat.mod_lt _ (by unfold cubeWidth; positivity)⟩

theorem row_column (R : ℕ) (k : Fin ((3*cubeWidth R^3)^2)) :
    k.val = (row R k).val*(3*cubeWidth R^3)+(column R k).val := by
  dsimp [row,column]
  simpa only [Nat.mul_comm] using (Nat.div_add_mod k.val (3*cubeWidth R^3)).symm

def positiveWords (R : ℕ) (material : Cell20 → ℚ) (z : ℚ) (D width : ℕ) :
    Vector (List Bool) ((3*cubeWidth R^3)^2) :=
  Vector.ofFn fun k => FixedWidth.bits width ((matrix R material z D).positive (row R k) (column R k)).bits

def negativeWords (R : ℕ) (material : Cell20 → ℚ) (z : ℚ) (D width : ℕ) :
    Vector (List Bool) ((3*cubeWidth R^3)^2) :=
  Vector.ofFn fun k => FixedWidth.bits width ((matrix R material z D).negative (row R k) (column R k)).bits

@[simp] theorem positiveWords_get (R : ℕ) (material : Cell20 → ℚ) (z : ℚ) (D width : ℕ)
    (k : Fin ((3*cubeWidth R^3)^2)) :
    (positiveWords R material z D width).get k =
      FixedWidth.bits width ((matrix R material z D).positive (row R k) (column R k)).bits := by
  simp [positiveWords,Vector.get,Fin.cast]

@[simp] theorem negativeWords_get (R : ℕ) (material : Cell20 → ℚ) (z : ℚ) (D width : ℕ)
    (k : Fin ((3*cubeWidth R^3)^2)) :
    (negativeWords R material z D width).get k =
      FixedWidth.bits width ((matrix R material z D).negative (row R k) (column R k)).bits := by
  simp [negativeWords,Vector.get,Fin.cast]

def slot (R : ℕ) (i j : Fin (3*cubeWidth R^3)) : Fin ((3*cubeWidth R^3)^2) :=
  Fin.cast (pow_two (3*cubeWidth R^3)).symm (matrixSlot i j)

@[simp] theorem slot_val (R : ℕ) (i j : Fin (3*cubeWidth R^3)) :
    (slot R i j).val = i.val*(3*cubeWidth R^3)+j.val := rfl

@[simp] theorem row_slot (R : ℕ) (i j : Fin (3*cubeWidth R^3)) : row R (slot R i j) = i := by
  apply Fin.ext
  change (i.val*(3*cubeWidth R^3)+j.val)/(3*cubeWidth R^3) = i.val
  apply Nat.div_eq_of_lt_le (by omega)
  nlinarith [j.isLt]

@[simp] theorem column_slot (R : ℕ) (i j : Fin (3*cubeWidth R^3)) : column R (slot R i j) = j := by
  apply Fin.ext
  change (i.val*(3*cubeWidth R^3)+j.val)%(3*cubeWidth R^3) = j.val
  simp [Nat.add_mod,Nat.mod_eq_of_lt j.isLt]

/-- The initializer's flattened representation decodes to the matrix used
by the actual Horner kernel, with the same row-major slot convention. -/
theorem words_values (R : ℕ) (material : Cell20 → ℚ) (z : ℚ) (D width : ℕ)
    (hwidth : MaterialTable.outputBits 34 (MaterialEntry.table material z D) ≤ width)
    (i j : Fin (3*cubeWidth R^3)) :
    addressValue ((positiveWords R material z D width).get (slot R i j)) =
        (matrix R material z D).positive i j ∧
    addressValue ((negativeWords R material z D width).get (slot R i j)) =
        (matrix R material z D).negative i j := by
  have h := MaterialEntry.channel_lengths material z D
    (entryKey (radixCubeEmbedding R i) (radixCubeEmbedding R j))
  rw [entryChannels_binding] at h
  change ((matrix R material z D).positive i j).bits.length+
    ((matrix R material z D).negative i j).bits.length ≤ _ at h
  simp only [positiveWords_get,negativeWords_get,row_slot,column_slot]
  rw [FixedWidth.bits_value _ _ (show ((matrix R material z D).positive i j).bits.length ≤ width by omega),
    FixedWidth.bits_value _ _ (show ((matrix R material z D).negative i j).bits.length ≤ width by omega),
    addressValue_bits,addressValue_bits]
  exact ⟨rfl,rfl⟩

end Maxwell.Cost.CalibrationMatrix.Generation
