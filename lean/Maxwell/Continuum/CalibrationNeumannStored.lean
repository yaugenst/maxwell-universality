import Maxwell.Continuum.CalibrationNeumannDescriptors

/-! The executed descriptor header and actual table bits furnish the full
starting invariant of the inverse machine. The overwritten workspace may
contain arbitrary bits; only the source, matrix and permanent zero slices
are read before their first write. -/

namespace Maxwell.Continuum.Calibration.NeumannMachine

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open Maxwell.Continuum.RationalDataflow
set_option maxHeartbeats 2000000

structure TableLayout {n : ℕ} (a b : PartArray.Table (tableSize n)) (heap : ℕ) : Prop where
  canonical : a.width=(addressValue a.width).bits
  width : b.width=a.width
  positive : addressValue a.basePositive=heap
  negative : addressValue a.baseNegative=heap+tableSize n*addressValue a.width
  copyPositive : addressValue b.basePositive=heap+3*tableSize n*addressValue a.width
  copyNegative : addressValue b.baseNegative=heap+4*tableSize n*addressValue a.width

theorem initial_stored {n D N : ℕ} (a b : PartArray.Table (tableSize n)) (heap : ℕ)
    (hw : 0<addressValue a.width) (s : BitRAMState) (hl : TableLayout a b heap)
    (hh : Descriptors.Header n (addressValue a.width) heap D N s)
    (hc : BankArray.Word s 101 a.clock)
    (hap : BitArray.Represents s.memory (addressValue a.basePositive) (addressValue a.width) a.positive)
    (han : BitArray.Represents s.memory (addressValue a.baseNegative) (addressValue a.width) a.negative)
    (hbp : BitArray.Represents s.memory (addressValue b.basePositive) (addressValue b.width) b.positive)
    (hbn : BitArray.Represents s.memory (addressValue b.baseNegative) (addressValue b.width) b.negative) :
    Horner.Stored (initialData a heap D hw) (initialWords a b heap s.memory) s := by
  refine ⟨?_,hc,hh.matrixPositive,hh.matrixNegative,hh.bases,
    hh.denominator,hh.numerator,?_,?_,?_⟩
  · change BankArray.Word s 100 a.width
    rw [hl.canonical]
    exact hh.widthWord
  · simpa only [initialData,addressValue_bits,paddedMatrixPositive,hl.positive] using
      represents_slice hap n (n*n) (by unfold tableSize; omega)
  · simpa only [initialData,addressValue_bits,paddedMatrixNegative,hl.negative,Nat.add_mul,Nat.add_assoc] using
      represents_slice han n (n*n) (by unfold tableSize; omega)
  · intro i
    fin_cases i
    all_goals norm_num [initialData,initialWords,vectorOffset]
    · simpa only [paddedSourcePositive,hl.positive,Nat.zero_mul,Nat.add_zero] using
        represents_slice hap 0 n (by unfold tableSize; omega)
    · simpa only [paddedSourceNegative,hl.negative,tableSize,Nat.zero_mul,Nat.add_zero] using
        represents_slice han 0 n (by unfold tableSize; omega)
    · simpa only [paddedZeroPositive,hl.positive] using
        represents_slice hap (n+n*n) n le_rfl
    · simpa only [paddedZeroNegative,hl.negative,tableSize,Nat.add_mul,Nat.add_assoc] using
        represents_slice han (n+n*n) n le_rfl
    · exact memoryWords_represents _ _ _ _
    · exact memoryWords_represents _ _ _ _
    · exact memoryWords_represents _ _ _ _
    · exact memoryWords_represents _ _ _ _
    · exact memoryWords_represents _ _ _ _
    · exact memoryWords_represents _ _ _ _
    · simpa only [paddedSourcePositive,hl.copyPositive,hl.width,tableSize,Nat.zero_mul,Nat.add_zero,
        Nat.mul_assoc] using represents_slice hbp 0 n (by unfold tableSize; omega)
    · simpa only [paddedSourceNegative,hl.copyNegative,hl.width,tableSize,Nat.zero_mul,Nat.add_zero,
        Nat.mul_assoc] using represents_slice hbn 0 n (by unfold tableSize; omega)

theorem header_workReady {n width heap D N B : ℕ} {s : BitRAMState}
    (hh : Descriptors.Header n width heap D N s) (hz : BankArray.Scratch s)
    (h7 : RationalAccumulator.Blank s 7) (h37 : RationalAccumulator.Blank s 37) :
    Horner.WorkReady n.bits B s := by
  have hblank (i : ℕ) (hi : i∈([102,103,104,106,108,109]:List ℕ)) :=
    (RationalAccumulator.zero_word_iff_blank s i).mp (hh.cursors i hi)
  refine ⟨[],rfl,by simp,⟨?_,hz,h7⟩,
    ⟨hh.cursors 102 (by simp),hh.cursors 103 (by simp)⟩,
    hh.cursors 104 (by simp),hh.dimension,
    hblank 106 (by simp),h37,hblank 108 (by simp),hblank 109 (by simp)⟩
  intro i hi hi'
  simpa only [dotValues,Function.update_apply,ite_self] using hh.accumulators i hi hi'

theorem header_ports {n D N : ℕ} (a : PartArray.Table (tableSize n)) (heap : ℕ)
    (hw : 0<addressValue a.width) {s : BitRAMState}
    (hh : Descriptors.Header n (addressValue a.width) heap D N s) :
    Horner.Ports (initialData a heap D hw) 10 11 5 4 s := by
  constructor
  · simpa [initialData,vectorOffset,tableSize,Nat.mul_assoc,BankArray.Word,RationalAccumulator.Word] using hh.inputPositive
  · simpa [initialData,vectorOffset,tableSize,Nat.mul_assoc,BankArray.Word,RationalAccumulator.Word] using hh.inputNegative
  · simpa [initialData,vectorOffset,tableSize,Nat.add_mul,Nat.mul_assoc,BankArray.Word,RationalAccumulator.Word] using hh.outputPositive
  · simpa [initialData,vectorOffset,tableSize,Nat.mul_assoc,BankArray.Word,RationalAccumulator.Word] using hh.outputNegative

theorem initial_ready {n D N B : ℕ} (a b : PartArray.Table (tableSize n)) (heap : ℕ)
    (hw : 0<addressValue a.width) (s : BitRAMState) (hl : TableLayout a b heap)
    (hh : Descriptors.Header n (addressValue a.width) heap D N s)
    (hc : BankArray.Word s 101 a.clock) (hz : BankArray.Scratch s)
    (h7 : RationalAccumulator.Blank s 7) (h37 : RationalAccumulator.Blank s 37)
    (hap : BitArray.Represents s.memory (addressValue a.basePositive) (addressValue a.width) a.positive)
    (han : BitArray.Represents s.memory (addressValue a.baseNegative) (addressValue a.width) a.negative)
    (hbp : BitArray.Represents s.memory (addressValue b.basePositive) (addressValue b.width) b.positive)
    (hbn : BitArray.Represents s.memory (addressValue b.baseNegative) (addressValue b.width) b.negative) :
    (initialSnapshot a b heap D hw s.memory).Ready n.bits B s :=
  ⟨header_workReady hh hz h7 h37,initial_stored a b heap hw s hl hh hc hap han hbp hbn,
    header_ports a heap hw hh⟩

#print axioms initial_stored
#print axioms initial_ready

end Maxwell.Continuum.Calibration.NeumannMachine
