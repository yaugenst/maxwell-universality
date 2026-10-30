import Maxwell.Continuum.CalibrationNeumannPaddedTable
import Maxwell.Continuum.CalibrationNeumannMachine

/-! A concrete memory layout for the shared-table inverse loop. Source,
matrix, and permanent zero arrays are slices of one converted table; the
second table supplies the duplicated live source. All work arrays occupy
separate intervals after those tables. -/

namespace Maxwell.Continuum.Calibration.NeumannMachine

open Maxwell.Cost Maxwell.Cost.CalibrationMatrix
open Maxwell.Continuum.RationalDataflow
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

def vectorOffset (n m : ℕ) (i : Fin 12) : ℕ :=
  let T := n+m+n
  if i=0 then 0 else if i=1 then T else if i=2 then n+m else if i=3 then T+n+m
  else if i=10 then 3*T else if i=11 then 4*T else 6*T+(i.val-4)*n

theorem vectorOffset_separated (n m : ℕ) (i j : Fin 12) (hij : i≠j) :
    IncidenceEncoding.Separated (vectorOffset n m i) n (vectorOffset n m j) n := by
  fin_cases i <;> fin_cases j <;>
    simp_all [vectorOffset,IncidenceEncoding.Separated] <;> omega

theorem matrixOffset_separated (n m : ℕ) (i : Fin 12) :
    IncidenceEncoding.Separated n m (vectorOffset n m i) n ∧
    IncidenceEncoding.Separated (n+m+n+n) m (vectorOffset n m i) n := by
  fin_cases i <;> norm_num [vectorOffset,IncidenceEncoding.Separated] <;> omega

theorem scaled_separated (heap width : ℕ) {a an b bn : ℕ}
    (h : IncidenceEncoding.Separated a an b bn) :
    IncidenceEncoding.Separated (heap+a*width) (an*width) (heap+b*width) (bn*width) := by
  rcases h with h | h
  · left
    have hh := Nat.mul_le_mul_right width h
    simpa only [Nat.add_mul,Nat.add_assoc] using Nat.add_le_add_left hh heap
  · right
    have hh := Nat.mul_le_mul_right width h
    simpa only [Nat.add_mul,Nat.add_assoc] using Nat.add_le_add_left hh heap

def initialData {n : ℕ} (a : PartArray.Table (tableSize n)) (heap D : ℕ)
    (hw : 0<addressValue a.width) : Horner.Data n where
  width := a.width
  clock := a.clock
  matrixPositiveBase := (heap+n*addressValue a.width).bits
  matrixNegativeBase := (heap+(tableSize n+n)*addressValue a.width).bits
  matrixPositive := paddedMatrixPositive a
  matrixNegative := paddedMatrixNegative a
  bases := fun i => (heap+vectorOffset n (n*n) i*addressValue a.width).bits
  K := D
  S := 1
  width_nonempty := a.width_pos
  width_positive := hw
  clock_length := a.clock_length
  separated := fun i j hij => by
    simp only [addressValue_bits]
    exact scaled_separated heap _ (vectorOffset_separated n (n*n) i j hij)
  matrixPositive_separated := fun i => by
    simp only [addressValue_bits]
    exact scaled_separated heap _ (matrixOffset_separated n (n*n) i).1
  matrixNegative_separated := fun i => by
    simp only [addressValue_bits]
    exact scaled_separated heap _ (matrixOffset_separated n (n*n) i).2

def memoryWords (memory : ℕ→Bool) (base width n : ℕ) : Vector (List Bool) n :=
  Vector.ofFn (fun i => MemoryWord.readBits memory (base+i.val*width) width)

theorem memoryWords_represents (memory : ℕ→Bool) (base width n : ℕ) :
    BitArray.Represents memory base width (memoryWords memory base width n) := by
  refine ⟨fun i => ?_,fun i j hj => ?_⟩
  · simp [memoryWords,Vector.get,Fin.cast]
  · simpa [memoryWords,Vector.get,Fin.cast] using
      (MemoryWord.readBits_getElem memory (base+i.val*width) width j hj).symm

def initialWords {n : ℕ} (a b : PartArray.Table (tableSize n)) (heap : ℕ) (memory : ℕ→Bool) :
    Fin 12→Vector (List Bool) n := fun i =>
  if i=0 then paddedSourcePositive a else if i=1 then paddedSourceNegative a
  else if i=2 then paddedZeroPositive a else if i=3 then paddedZeroNegative a
  else if i=10 then paddedSourcePositive b else if i=11 then paddedSourceNegative b
  else memoryWords memory (heap+vectorOffset n (n*n) i*addressValue a.width) (addressValue a.width) n

def initialSnapshot {n : ℕ} (a b : PartArray.Table (tableSize n)) (heap D : ℕ)
    (hw : 0<addressValue a.width) (memory : ℕ→Bool) : Snapshot n :=
  ⟨initialData a heap D hw,initialWords a b heap memory⟩

theorem initialSnapshot_decodes {n : ℕ} (coeff : CoefficientIndex n→Parts)
    (a b : PartArray.Table (tableSize n)) (heap : ℕ) (hw : 0<addressValue a.width)
    (memory : ℕ→Bool)
    (ha : ∀ i, a.get i=SharedTable.integerParts (paddedCoefficients coeff) i)
    (hb : ∀ i, b.get i=a.get i) :
    (initialSnapshot a b heap (SharedTable.denominator coeff) hw memory).Decodes
      (rawMatrix coeff) (SharedTable.denominator coeff) (rawSource coeff,rawSource coeff) := by
  have hb' (i) : b.get i=SharedTable.integerParts (paddedCoefficients coeff) i := (hb i).trans (ha i)
  refine ⟨⟨fun i j => (padded_matrix_value coeff a ha i j).1,
    fun i j => (padded_matrix_value coeff a ha i j).2⟩,rfl,rfl,?_,?_,?_⟩
  · apply congrArg₂ Channels.mk <;> funext i
    · simpa [Horner.channels,initialSnapshot,initialWords,rawSource] using
        (padded_source_value coeff a ha i).1
    · simpa [Horner.channels,initialSnapshot,initialWords,rawSource] using
        (padded_source_value coeff a ha i).2
  · apply congrArg₂ Channels.mk <;> funext i
    · simpa [Horner.channels,initialSnapshot,initialWords,rawSource] using
        (padded_source_value coeff b hb' i).1
    · simpa [Horner.channels,initialSnapshot,initialWords,rawSource] using
        (padded_source_value coeff b hb' i).2
  · apply congrArg₂ Channels.mk <;> funext i
    · simpa [Horner.channels,initialSnapshot,initialWords,zeroChannels] using
        (padded_zero_value coeff a ha i).1
    · simpa [Horner.channels,initialSnapshot,initialWords,zeroChannels] using
        (padded_zero_value coeff a ha i).2

#print axioms vectorOffset_separated
#print axioms memoryWords_represents
#print axioms initialSnapshot_decodes

end Maxwell.Continuum.Calibration.NeumannMachine
