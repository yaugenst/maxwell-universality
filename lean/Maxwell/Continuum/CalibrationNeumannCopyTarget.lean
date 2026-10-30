import Maxwell.Continuum.CalibrationNeumannCopied

/-! The copy destination is described by the memory that is actually
present. No initialized or zero-filled scratch-array premise is required. -/

namespace Maxwell.Continuum.Calibration.NeumannMachine

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open Maxwell.Continuum.RationalDataflow
set_option maxHeartbeats 2000000

structure SourceLayout {n : ℕ} (a : PartArray.Table (tableSize n)) (heap : ℕ) : Prop where
  canonical : a.width = (addressValue a.width).bits
  positive : a.basePositive = heap.bits
  negative : a.baseNegative = (heap+tableSize n*addressValue a.width).bits
  denominator : a.baseDenominator = (heap+2*tableSize n*addressValue a.width).bits

def copyTarget {n : ℕ} (a : PartArray.Table (tableSize n)) (heap : ℕ) (memory : ℕ → Bool) :
    PartArray.Table (tableSize n) where
  width := a.width
  clock := a.clock
  basePositive := (heap+3*tableSize n*addressValue a.width).bits
  baseNegative := (heap+4*tableSize n*addressValue a.width).bits
  baseDenominator := (heap+5*tableSize n*addressValue a.width).bits
  positive := memoryWords memory (heap+3*tableSize n*addressValue a.width) (addressValue a.width) (tableSize n)
  negative := memoryWords memory (heap+4*tableSize n*addressValue a.width) (addressValue a.width) (tableSize n)
  denominator := memoryWords memory (heap+5*tableSize n*addressValue a.width) (addressValue a.width) (tableSize n)
  width_pos := a.width_pos
  clock_length := a.clock_length

theorem copyTarget_layout {n : ℕ} (a : PartArray.Table (tableSize n)) (heap : ℕ)
    (memory : ℕ → Bool) (h : SourceLayout a heap) : TableLayout a (copyTarget a heap memory) heap := by
  exact ⟨h.canonical,rfl,by simp only [h.positive,addressValue_bits],
    by simp only [h.negative,addressValue_bits],by simp [copyTarget],by simp [copyTarget]⟩

theorem copyTarget_separated {n : ℕ} (a : PartArray.Table (tableSize n)) (heap : ℕ)
    (memory : ℕ → Bool) : (copyTarget a heap memory).Separated := by
  simp only [PartArray.Table.Separated,copyTarget,addressValue_bits,IncidenceEncoding.Separated,
    Nat.mul_assoc]
  constructor
  · left; omega
  constructor <;> left <;> omega

theorem copyTarget_disjoint {n : ℕ} (a : PartArray.Table (tableSize n)) (heap : ℕ)
    (memory : ℕ → Bool) (h : SourceLayout a heap) : a.SeparatedFrom (copyTarget a heap memory) := by
  simp only [PartArray.Table.SeparatedFrom,copyTarget,h.positive,h.negative,h.denominator,
    List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
    addressValue_bits,IncidenceEncoding.Separated,Nat.mul_assoc]
  exact ⟨⟨Or.inl (by omega),Or.inl (by omega),Or.inl (by omega)⟩,
    ⟨Or.inl (by omega),Or.inl (by omega),Or.inl (by omega)⟩,
    ⟨Or.inl (by omega),Or.inl (by omega),Or.inl (by omega)⟩⟩

#print axioms copyTarget_disjoint

end Maxwell.Continuum.Calibration.NeumannMachine
