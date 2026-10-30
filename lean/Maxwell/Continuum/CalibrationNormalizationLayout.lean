import Maxwell.Continuum.CalibrationNormalizationAllocation
import Maxwell.Continuum.CalibrationNormalizationWidths
import Maxwell.Continuum.CalibrationNormalizedArrayState

/-! The allocated output table has the required write width and is disjoint
from the actual current vector buffers when placed after their last cell. -/

namespace Maxwell.Continuum.Calibration.PowerMachine.BufferNorm.Allocation

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open RationalDataflow
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

theorem outputWidth_pos (n K P B : ℕ) : 0<outputWidth n K P B := by
  unfold outputWidth
  omega

def outputTable (n K P B heap : ℕ) (memory : ℕ → Bool) : PartArray.Table n :=
  Profile.Runtime.memoryTable n (outputWidth n K P B) heap (outputWidth_pos n K P B) memory

theorem outputWidth_bits (n K P B : ℕ) :
    (outputWidth n K P B).bits.length≤normalizationWidth n K P B+P+21 := by
  have small (m : ℕ) : m.bits.length≤m := by
    rw [Nat.size_eq_bits_len,Nat.size_le]
    exact Nat.lt_two_pow_self
  have hm := RationalAccumulator.bits_mul_le 32 (normalizationWidth n K P B)
  have hp := RationalAccumulator.bits_mul_le 32 P
  have ha := RationalAccumulator.bits_add_le (32*normalizationWidth n K P B) (32*P)
  have hb := RationalAccumulator.bits_add_le (32*normalizationWidth n K P B+32*P) 64
  norm_num only [show (32:ℕ).bits.length=6 from rfl,show (64:ℕ).bits.length=7 from rfl] at hm hp hb
  unfold outputWidth
  have hn := small (normalizationWidth n K P B)
  have hP := small P
  omega

theorem outputTable_metadata (n K P B heap : ℕ) (memory : ℕ → Bool)
    (hheap : heap.bits.length≤B) : (outputTable n K P B heap memory).MetadataWidth (outputWidth n K P B) := by
  apply Profile.Runtime.memoryTable_metadata n (outputWidth n K P B) heap (outputWidth n K P B)
    (outputWidth_pos n K P B) memory le_rfl
  have hn : n.bits.length≤n := by
    rw [Nat.size_eq_bits_len,Nat.size_le]
    exact Nat.lt_two_pow_self
  have hw := outputWidth_bits n K P B
  unfold outputWidth normalizationWidth NeumannMachine.StoredPairing.workWidth at hw ⊢
  omega

theorem outputTable_slot (n K P B heap : ℕ) (memory : ℕ → Bool) :
    addressValue (outputTable n K P B heap memory).width=outputWidth n K P B := by
  exact addressValue_bits _

theorem outputTable_separated (n K P B heap : ℕ) (memory : ℕ → Bool) :
    (outputTable n K P B heap memory).Separated :=
  Profile.Runtime.memoryTable_separated _ _ _ _ _

theorem outputTable_separatedFrom {n : ℕ} (a : CalibrationMatrix.Data n n)
    (K P B heap : ℕ) (memory : ℕ → Bool)
    (hheap : ∀ x∈[a.matrixPositiveBase,a.matrixNegativeBase,a.vectorPositiveBase,a.vectorNegativeBase],
      addressValue x+n*addressValue a.width≤heap) :
    NormalizedEntry.SeparatedFrom a (outputTable n K P B heap memory) := by
  intro x hx y hy
  have h := hheap x hx
  simp only [outputTable,Profile.Runtime.memoryTable,List.mem_cons,List.not_mem_nil,or_false] at hy
  rcases hy with rfl|rfl|rfl <;>
    simp only [outputTable,Profile.Runtime.memoryTable,addressValue_bits,IncidenceEncoding.Separated] <;>
    left <;> omega

theorem buffer_ready_frame {n B : ℕ} {b : Buffers n} {count : List Bool} {s t : BitRAMState}
    {changes : Finset ℕ} (hb : b.Ready count B s) (f : BinaryPrecision.Frame changes s t)
    (hout : ∀ i, 4 ≤ i → i<200 → i∉changes) (hz : NatAssign.Scratch t) : b.Ready count B t := by
  obtain ⟨vi,hvi,hvl,cal,stored,indices,out,countWord,blank,h37,h108,h109⟩ := hb
  have keep (i : ℕ) (hi : 4 ≤ i) (hbig : i<200) : t.tapes i=s.tapes i := f.tapes i (hout i hi hbig)
  have scratch : BankArray.Scratch t :=
    ⟨hz 0 (by decide),hz 1 (by decide),hz 2 (by decide),hz 3 (by decide),
      RationalAccumulator.blank_of_eq (keep 5 (by decide) (by decide)) cal.2.1.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keep 6 (by decide) (by decide)) cal.2.1.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keep 8 (by decide) (by decide)) cal.2.1.2.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keep 9 (by decide) (by decide)) cal.2.1.2.2.2.2.2.2.2⟩
  have bank : RationalAccumulator.Bank t (dotValues 0 0) := by
    intro i hlo hhi
    exact RationalAccumulator.word_of_eq (keep i (by omega) (by omega)) (cal.1 i hlo hhi)
  refine ⟨vi,hvi,hvl,⟨bank,scratch,RationalAccumulator.blank_of_eq (keep 7 (by decide) (by decide)) cal.2.2⟩,
    ?_,⟨BankArray.word_of_eq (keep 102 (by decide) (by decide)) indices.1,
      BankArray.word_of_eq (keep 103 (by decide) (by decide)) indices.2⟩,
    out.of_memory f.memory (fun i hi => keep i (by omega) (by omega)),
    BankArray.word_of_eq (keep 107 (by decide) (by decide)) countWord,
    RationalAccumulator.blank_of_eq (keep 106 (by decide) (by decide)) blank,
    RationalAccumulator.blank_of_eq (keep 37 (by decide) (by decide)) h37,
    RationalAccumulator.blank_of_eq (keep 108 (by decide) (by decide)) h108,
    RationalAccumulator.blank_of_eq (keep 109 (by decide) (by decide)) h109⟩
  exact ⟨BankArray.word_of_eq (keep 100 (by decide) (by decide)) stored.width,
    BankArray.word_of_eq (keep 101 (by decide) (by decide)) stored.clock,
    BankArray.word_of_eq (keep 110 (by decide) (by decide)) stored.matrixPositiveBase,
    BankArray.word_of_eq (keep 111 (by decide) (by decide)) stored.matrixNegativeBase,
    BankArray.word_of_eq (keep 112 (by decide) (by decide)) stored.vectorPositiveBase,
    BankArray.word_of_eq (keep 113 (by decide) (by decide)) stored.vectorNegativeBase,
    by simpa only [f.memory] using stored.matrixPositive,
    by simpa only [f.memory] using stored.matrixNegative,
    by simpa only [f.memory] using stored.vectorPositive,
    by simpa only [f.memory] using stored.vectorNegative⟩

#print axioms outputTable_metadata
#print axioms outputTable_separatedFrom
#print axioms buffer_ready_frame

end Maxwell.Continuum.Calibration.PowerMachine.BufferNorm.Allocation
