import Maxwell.Continuum.CalibrationNeumannRawTable
import Maxwell.Continuum.RationalDataflowSharedTableMachine
import Mathlib.Logic.Equiv.Fin.Basic

/-! Literal contiguous views of the executed shared-denominator table.
The source prefix and row-major matrix suffix retain their actual bit-memory
representation, so the inverse loop can reuse them without copying the matrix. -/

namespace Maxwell.Continuum.Calibration.NeumannMachine

open Maxwell.Cost Maxwell.Cost.CalibrationMatrix
open Maxwell.Continuum.RationalDataflow
open scoped BigOperators

set_option maxHeartbeats 1500000

def flatIndex (n : ℕ) : CoefficientIndex n ≃ Fin (n+n*n) :=
  (Equiv.sumCongr (Equiv.refl (Fin n)) finProdFinEquiv).trans finSumFinEquiv

theorem flatIndex_source (n : ℕ) (i : Fin n) :
    flatIndex n (.inl i)=Fin.castAdd (n*n) i := rfl

theorem flatIndex_matrix (n : ℕ) (i j : Fin n) :
    flatIndex n (.inr (i,j))=Fin.natAdd n (matrixSlot i j) := by
  apply Fin.ext
  change n+(j.val+n*i.val)=n+(i.val*n+j.val)
  ac_rfl

def flatCoefficients {n : ℕ} (a : CoefficientIndex n→Parts) : Fin (n+n*n)→Parts :=
  fun i => a ((flatIndex n).symm i)

theorem flatCoefficients_index {n : ℕ} (a : CoefficientIndex n→Parts) (i : CoefficientIndex n) :
    flatCoefficients a (flatIndex n i)=a i := by simp only [flatCoefficients,Equiv.symm_apply_apply]

theorem denominator_flat {n : ℕ} (a : CoefficientIndex n→Parts) :
    SharedTable.denominator (flatCoefficients a)=SharedTable.denominator a := by
  symm
  apply Fintype.prod_equiv (flatIndex n)
  intro i
  rw [flatCoefficients_index]

theorem integerParts_flat {n : ℕ} (a : CoefficientIndex n→Parts) (i : CoefficientIndex n) :
    SharedTable.integerParts (flatCoefficients a) (flatIndex n i)=SharedTable.integerParts a i := by
  simp only [SharedTable.integerParts,flatCoefficients_index,denominator_flat]

def wordSlice {N : ℕ} (words : Vector (List Bool) N) (start count : ℕ)
    (h : start+count≤N) : Vector (List Bool) count :=
  Vector.ofFn (fun i => words.get ⟨start+i.val,by omega⟩)

theorem wordSlice_get {N : ℕ} (words : Vector (List Bool) N) (start count : ℕ)
    (h : start+count≤N) (i : Fin count) :
    (wordSlice words start count h).get i=words.get ⟨start+i.val,by omega⟩ := by
  simp [wordSlice,Vector.get,Fin.cast]

theorem represents_slice {N : ℕ} {words : Vector (List Bool) N}
    {memory : ℕ→Bool} {base width : ℕ} (hwords : BitArray.Represents memory base width words)
    (start count : ℕ) (h : start+count≤N) :
    BitArray.Represents memory (base+start*width) width (wordSlice words start count h) := by
  refine ⟨fun i => by rw [wordSlice_get]; exact hwords.length _,?_⟩
  intro i j hj
  have hh := hwords.bits ⟨start+i.val,by omega⟩ j hj
  simpa only [wordSlice_get,Nat.add_mul,Nat.add_assoc] using hh

def sourceView {n : ℕ} (a : PartArray.Table (n+n*n)) : PartArray.Table n where
  width := a.width
  basePositive := a.basePositive
  baseNegative := a.baseNegative
  baseDenominator := a.baseDenominator
  clock := a.clock
  positive := wordSlice a.positive 0 n (by omega)
  negative := wordSlice a.negative 0 n (by omega)
  denominator := wordSlice a.denominator 0 n (by omega)
  width_pos := a.width_pos
  clock_length := a.clock_length

theorem sourceView_get {n : ℕ} (a : PartArray.Table (n+n*n)) (i : Fin n) :
    (sourceView a).get i=a.get (Fin.castAdd (n*n) i) := by
  simp only [sourceView,PartArray.Table.get,wordSlice_get,Nat.zero_add]
  rfl

theorem sourceView_ready {n : ℕ} {a : PartArray.Table (n+n*n)} {s : Structured.Store}
    (h : a.Ready s) : (sourceView a).Ready s := by
  refine ⟨h.scratch,h.seven,h.width,h.basePositive,h.baseNegative,h.baseDenominator,h.clock,?_,?_,?_⟩
  · simpa only [sourceView,Nat.zero_mul,Nat.add_zero] using represents_slice h.positive 0 n (by omega)
  · simpa only [sourceView,Nat.zero_mul,Nat.add_zero] using represents_slice h.negative 0 n (by omega)
  · simpa only [sourceView,Nat.zero_mul,Nat.add_zero] using represents_slice h.denominator 0 n (by omega)

def matrixPositiveView {n : ℕ} (a : PartArray.Table (n+n*n)) : Vector (List Bool) (n*n) :=
  wordSlice a.positive n (n*n) le_rfl

def matrixNegativeView {n : ℕ} (a : PartArray.Table (n+n*n)) : Vector (List Bool) (n*n) :=
  wordSlice a.negative n (n*n) le_rfl

theorem matrixPositiveView_represents {n : ℕ} {a : PartArray.Table (n+n*n)}
    {s : Structured.Store} (h : a.OutputReady s) :
    BitArray.Represents s.val.memory (addressValue a.basePositive+n*addressValue a.width)
      (addressValue a.width) (matrixPositiveView a) := represents_slice h.positive n (n*n) le_rfl

theorem matrixNegativeView_represents {n : ℕ} {a : PartArray.Table (n+n*n)}
    {s : Structured.Store} (h : a.OutputReady s) :
    BitArray.Represents s.val.memory (addressValue a.baseNegative+n*addressValue a.width)
      (addressValue a.width) (matrixNegativeView a) := represents_slice h.negative n (n*n) le_rfl

theorem shared_source_value {n : ℕ} (a : CoefficientIndex n→Parts)
    (b : PartArray.Table (n+n*n))
    (hb : ∀ i, b.get i=SharedTable.integerParts (flatCoefficients a) i) (i : Fin n) :
    (sourceView b).get i=SharedTable.integerParts a (.inl i) := by
  rw [sourceView_get,←flatIndex_source,hb,integerParts_flat]

theorem shared_matrix_value {n : ℕ} (a : CoefficientIndex n→Parts)
    (b : PartArray.Table (n+n*n))
    (hb : ∀ i, b.get i=SharedTable.integerParts (flatCoefficients a) i) (i j : Fin n) :
    addressValue ((matrixPositiveView b).get (matrixSlot i j))=(rawMatrix a).positive i j ∧
    addressValue ((matrixNegativeView b).get (matrixSlot i j))=(rawMatrix a).negative i j := by
  have h := hb (flatIndex n (.inr (i,j)))
  rw [integerParts_flat,flatIndex_matrix] at h
  refine ⟨?_,?_⟩
  · simpa only [PartArray.Table.get,matrixPositiveView,wordSlice_get,rawMatrix,Fin.natAdd] using congrArg Parts.positive h
  · simpa only [PartArray.Table.get,matrixNegativeView,wordSlice_get,rawMatrix,Fin.natAdd] using congrArg Parts.negative h

#print axioms denominator_flat
#print axioms sourceView_ready
#print axioms shared_matrix_value

end Maxwell.Continuum.Calibration.NeumannMachine
