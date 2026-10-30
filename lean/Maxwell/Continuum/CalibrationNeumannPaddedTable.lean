import Maxwell.Continuum.CalibrationNeumannFlatTable

/-! The shared coefficient table also contains the literal zero entries
used by the inverse loop. Their denominator is one, so executing the same
table conversion creates the permanent zero pair without changing the
shared denominator or assuming preinitialized memory. -/

namespace Maxwell.Continuum.Calibration.NeumannMachine

open Maxwell.Cost Maxwell.Cost.CalibrationMatrix
open Maxwell.Continuum.RationalDataflow
open scoped BigOperators
set_option maxHeartbeats 1500000

def tableSize (n : ℕ) : ℕ := n+n*n+n

def paddedCoefficients {n : ℕ} (a : CoefficientIndex n→Parts) : Fin (tableSize n)→Parts :=
  Fin.addCases (flatCoefficients a) (fun _ : Fin n => Parts.literal 0)

theorem padded_prefix {n : ℕ} (a : CoefficientIndex n→Parts) (i : Fin (n+n*n)) :
    paddedCoefficients a (Fin.castAdd n i)=flatCoefficients a i := by
  simp [paddedCoefficients]

theorem padded_zero {n : ℕ} (a : CoefficientIndex n→Parts) (i : Fin n) :
    paddedCoefficients a (Fin.natAdd (n+n*n) i)=Parts.literal 0 := by
  simp [paddedCoefficients]

theorem denominator_padded {n : ℕ} (a : CoefficientIndex n→Parts) :
    SharedTable.denominator (paddedCoefficients a)=SharedTable.denominator a := by
  change (∏ i : Fin ((n+n*n)+n), (paddedCoefficients a i).denominator)=_
  rw [Fin.prod_univ_add]
  simp only [padded_prefix,padded_zero,Parts.literal,Rat.num_zero,Int.toNat_zero,neg_zero,
    Rat.den_zero,Finset.prod_const_one,mul_one]
  exact denominator_flat a

theorem padded_valid {n : ℕ} (a : CoefficientIndex n→Parts) (ha : ∀ i, (a i).Valid)
    (i : Fin (tableSize n)) : (paddedCoefficients a i).Valid := by
  refine Fin.addCases ?_ ?_ i
  · intro j
    rw [padded_prefix]
    exact ha _
  · intro j
    rw [padded_zero]
    exact Parts.literal_valid 0

theorem padded_width {n : ℕ} (a : CoefficientIndex n→Parts) (W : ℕ)
    (hW : 0<W) (ha : ∀ i, (a i).Width W) (i : Fin (tableSize n)) :
    (paddedCoefficients a i).Width W := by
  refine Fin.addCases ?_ ?_ i
  · intro j
    rw [padded_prefix]
    exact ha _
  · intro j
    rw [padded_zero]
    norm_num [Parts.literal,Parts.Width]
    exact hW

theorem integerParts_padded {n : ℕ} (a : CoefficientIndex n→Parts) (i : CoefficientIndex n) :
    SharedTable.integerParts (paddedCoefficients a) (Fin.castAdd n (flatIndex n i))=
      SharedTable.integerParts a i := by
  simp only [SharedTable.integerParts,padded_prefix,flatCoefficients_index,denominator_padded]

theorem integerParts_padded_zero {n : ℕ} (a : CoefficientIndex n→Parts) (i : Fin n) :
    SharedTable.integerParts (paddedCoefficients a) (Fin.natAdd (n+n*n) i)=Parts.literal 0 := by
  simp only [SharedTable.integerParts,padded_zero,Parts.literal,Rat.num_zero,Int.toNat_zero,
    neg_zero,Rat.den_zero,Nat.zero_mul]

def paddedSourcePositive {n : ℕ} (a : PartArray.Table (tableSize n)) : Vector (List Bool) n :=
  wordSlice a.positive 0 n (by unfold tableSize; omega)

def paddedSourceNegative {n : ℕ} (a : PartArray.Table (tableSize n)) : Vector (List Bool) n :=
  wordSlice a.negative 0 n (by unfold tableSize; omega)

def paddedMatrixPositive {n : ℕ} (a : PartArray.Table (tableSize n)) : Vector (List Bool) (n*n) :=
  wordSlice a.positive n (n*n) (by unfold tableSize; omega)

def paddedMatrixNegative {n : ℕ} (a : PartArray.Table (tableSize n)) : Vector (List Bool) (n*n) :=
  wordSlice a.negative n (n*n) (by unfold tableSize; omega)

def paddedZeroPositive {n : ℕ} (a : PartArray.Table (tableSize n)) : Vector (List Bool) n :=
  wordSlice a.positive (n+n*n) n le_rfl

def paddedZeroNegative {n : ℕ} (a : PartArray.Table (tableSize n)) : Vector (List Bool) n :=
  wordSlice a.negative (n+n*n) n le_rfl

theorem padded_source_value {n : ℕ} (a : CoefficientIndex n→Parts)
    (b : PartArray.Table (tableSize n))
    (hb : ∀ i, b.get i=SharedTable.integerParts (paddedCoefficients a) i) (i : Fin n) :
    addressValue ((paddedSourcePositive b).get i)=(rawSource a).positive i ∧
    addressValue ((paddedSourceNegative b).get i)=(rawSource a).negative i := by
  have h := hb (Fin.castAdd n (flatIndex n (.inl i)))
  rw [integerParts_padded,flatIndex_source] at h
  refine ⟨?_,?_⟩
  · simpa [PartArray.Table.get,paddedSourcePositive,wordSlice,rawSource,Vector.get,Fin.cast,Fin.castAdd,Fin.castLE,tableSize]
      using congrArg Parts.positive h
  · simpa [PartArray.Table.get,paddedSourceNegative,wordSlice,rawSource,Vector.get,Fin.cast,Fin.castAdd,Fin.castLE,tableSize]
      using congrArg Parts.negative h

theorem padded_matrix_value {n : ℕ} (a : CoefficientIndex n→Parts)
    (b : PartArray.Table (tableSize n))
    (hb : ∀ i, b.get i=SharedTable.integerParts (paddedCoefficients a) i) (i j : Fin n) :
    addressValue ((paddedMatrixPositive b).get (matrixSlot i j))=(rawMatrix a).positive i j ∧
    addressValue ((paddedMatrixNegative b).get (matrixSlot i j))=(rawMatrix a).negative i j := by
  have h := hb (Fin.castAdd n (flatIndex n (.inr (i,j))))
  rw [integerParts_padded,flatIndex_matrix] at h
  refine ⟨?_,?_⟩
  · simpa [PartArray.Table.get,paddedMatrixPositive,wordSlice,rawMatrix,Vector.get,Fin.cast,Fin.natAdd,Fin.castAdd,Fin.castLE,tableSize]
      using congrArg Parts.positive h
  · simpa [PartArray.Table.get,paddedMatrixNegative,wordSlice,rawMatrix,Vector.get,Fin.cast,Fin.natAdd,Fin.castAdd,Fin.castLE,tableSize]
      using congrArg Parts.negative h

theorem padded_zero_value {n : ℕ} (a : CoefficientIndex n→Parts)
    (b : PartArray.Table (tableSize n))
    (hb : ∀ i, b.get i=SharedTable.integerParts (paddedCoefficients a) i) (i : Fin n) :
    addressValue ((paddedZeroPositive b).get i)=0 ∧
    addressValue ((paddedZeroNegative b).get i)=0 := by
  have h := hb (Fin.natAdd (n+n*n) i)
  rw [integerParts_padded_zero] at h
  refine ⟨?_,?_⟩
  · simpa only [PartArray.Table.get,paddedZeroPositive,tableSize,wordSlice_get,Fin.natAdd,Parts.literal,
      Rat.num_zero,Int.toNat_zero] using congrArg Parts.positive h
  · simpa only [PartArray.Table.get,paddedZeroNegative,tableSize,wordSlice_get,Fin.natAdd,Parts.literal,
      Rat.num_zero,neg_zero,Int.toNat_zero] using congrArg Parts.negative h

#print axioms denominator_padded
#print axioms padded_source_value
#print axioms padded_matrix_value
#print axioms padded_zero_value

end Maxwell.Continuum.Calibration.NeumannMachine
