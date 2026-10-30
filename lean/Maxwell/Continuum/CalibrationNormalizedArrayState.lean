import Maxwell.Continuum.CalibrationNormalizedEntryWrite
import Maxwell.Continuum.RationalDataflowSharedMapState

/-! Raw width and disjoint-memory invariants for the normalization output
pass, derived from the actual current buffer and the shared scale. -/

namespace Maxwell.Continuum.Calibration.PowerMachine.NormalizedEntry

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open RationalDataflow RationalDataflow.PartArray
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def SeparatedFrom {n : ℕ} (a : CalibrationMatrix.Data n n) (b : Table n) : Prop :=
  ∀ x∈[a.matrixPositiveBase,a.matrixNegativeBase,a.vectorPositiveBase,a.vectorNegativeBase],
  ∀ y∈[b.basePositive,b.baseNegative,b.baseDenominator],
    IncidenceEncoding.Separated (addressValue x) (n*addressValue a.width)
      (addressValue y) (n*addressValue b.width)

theorem stored_write_frame {n : ℕ} {a : CalibrationMatrix.Data n n} {b : Table n} {s t : Store}
    (h : CalibrationMatrix.Stored a s.val) (hsep : SeparatedFrom a b) (i : Fin n) (x : Parts)
    (hm : t.val.memory=b.writeMemory i x s.val.memory) (f : BankArray.FrameExcept 37 s.val t.val) :
    CalibrationMatrix.Stored a t.val := by
  have keep (j : ℕ) (hj : 100 ≤ j) := f.2.2.2.1 j (Or.inr (by omega)) (by omega)
  refine ⟨BankArray.word_of_eq (keep _ (by decide)) h.width,
    BankArray.word_of_eq (keep _ (by decide)) h.clock,
    BankArray.word_of_eq (keep _ (by decide)) h.matrixPositiveBase,
    BankArray.word_of_eq (keep _ (by decide)) h.matrixNegativeBase,
    BankArray.word_of_eq (keep _ (by decide)) h.vectorPositiveBase,
    BankArray.word_of_eq (keep _ (by decide)) h.vectorNegativeBase,?_,?_,?_,?_⟩
  · rw [hm]
    exact b.writeMemory_preserves i x h.matrixPositive (hsep _ (by simp))
  · rw [hm]
    exact b.writeMemory_preserves i x h.matrixNegative (hsep _ (by simp))
  · rw [hm]
    exact b.writeMemory_preserves i x h.vectorPositive (hsep _ (by simp))
  · rw [hm]
    exact b.writeMemory_preserves i x h.vectorNegative (hsep _ (by simp))

theorem stored_count_frame {n : ℕ} {a : CalibrationMatrix.Data n n} {s t : Store}
    (h : CalibrationMatrix.Stored a s.val) (f : CountedShifted.Frame 140 s t) :
    CalibrationMatrix.Stored a t.val :=
  ⟨BankArray.word_of_eq (f.2.2.2.2.2.1 100 (by decide)) h.width,
    BankArray.word_of_eq (f.2.2.2.2.2.1 101 (by decide)) h.clock,
    BankArray.word_of_eq (f.2.2.2.2.2.1 110 (by decide)) h.matrixPositiveBase,
    BankArray.word_of_eq (f.2.2.2.2.2.1 111 (by decide)) h.matrixNegativeBase,
    BankArray.word_of_eq (f.2.2.2.2.2.1 112 (by decide)) h.vectorPositiveBase,
    BankArray.word_of_eq (f.2.2.2.2.2.1 113 (by decide)) h.vectorNegativeBase,
    by simpa only [f.2.2.1] using h.matrixPositive,
    by simpa only [f.2.2.1] using h.matrixNegative,
    by simpa only [f.2.2.1] using h.vectorPositive,
    by simpa only [f.2.2.1] using h.vectorNegative⟩

theorem bank_count_frame {v : ℕ → ℕ} {s t : Store}
    (h : NatAssign.Bank ids v s.val) (f : CountedShifted.Frame 140 s t) :
    NatAssign.Bank ids v t.val := by
  intro i hi
  have hn : i≠140 := by
    simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  exact RationalAccumulator.word_of_eq (f.2.2.2.2.2.1 i hn) (h i hi)

theorem output_read_frame {n : ℕ} {a : Table n} {s t : Store} (h : a.OutputReady s)
    (f : Frame s.val t.val) (hz : BankArray.Scratch t.val) (h7 : Blank t.val 7) :
    a.OutputReady t := by
  apply h.transfer f.memory _ hz h7
  intro i hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  apply f.tapes i <;> omega

theorem output_count_frame {n : ℕ} {a : Table n} {s t : Store} (h : a.OutputReady s)
    (f : CountedShifted.Frame 140 s t) : a.OutputReady t := by
  have keep (i : ℕ) (hi : i≠140) := f.2.2.2.2.2.1 i hi
  have hz : BankArray.Scratch t.val := by
    rcases h.scratch with ⟨h0,h1,h2,h3,h5,h6,h8,h9⟩
    exact ⟨RationalAccumulator.blank_of_eq (keep 0 (by decide)) h0,
      RationalAccumulator.blank_of_eq (keep 1 (by decide)) h1,
      RationalAccumulator.blank_of_eq (keep 2 (by decide)) h2,
      RationalAccumulator.blank_of_eq (keep 3 (by decide)) h3,
      RationalAccumulator.blank_of_eq (keep 5 (by decide)) h5,
      RationalAccumulator.blank_of_eq (keep 6 (by decide)) h6,
      RationalAccumulator.blank_of_eq (keep 8 (by decide)) h8,
      RationalAccumulator.blank_of_eq (keep 9 (by decide)) h9⟩
  apply h.transfer f.2.2.1 _ hz (RationalAccumulator.blank_of_eq (keep 7 (by decide)) h.seven)
  intro i hi
  apply keep i
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  omega

theorem entry_width {m n : ℕ} (a : CalibrationMatrix.Data m n) (scale denominator B : ℕ)
    (hscale : addressValue a.width+scale.bits.length≤B) (hden : denominator.bits.length≤B)
    {s : BitRAMState} (ha : CalibrationMatrix.Stored a s) (i : Fin n) :
    (entry a scale denominator i).Width B := by
  have hp := (canonical_length_le _).trans (ha.vectorPositive.length i).le
  have hm := (canonical_length_le _).trans (ha.vectorNegative.length i).le
  have bp := RationalAccumulator.bits_mul_le scale (addressValue (a.vectorPositive.get i))
  have bm := RationalAccumulator.bits_mul_le scale (addressValue (a.vectorNegative.get i))
  exact ⟨by change (scale*addressValue (a.vectorPositive.get i)).bits.length≤B; omega,
    by change (scale*addressValue (a.vectorNegative.get i)).bits.length≤B; omega,hden⟩

theorem values_width {m n : ℕ} (a : CalibrationMatrix.Data m n) (i : Fin n)
    (v : ℕ → ℕ) (B : ℕ) (hv : ∀ k∈ids, (v k).bits.length≤B)
    (he : (entry a (v 551) (v 552) i).Width B) :
    ∀ k∈ids, (values a i v k).bits.length≤B := by
  intro k hk
  by_cases h560 : k=560
  · subst k
    simpa only [values,Function.update_of_ne (by decide : (560:ℕ)≠561),Function.update_self] using he.1
  by_cases h561 : k=561
  · subst k
    simpa only [values,Function.update_self] using he.2.1
  simpa only [values,Function.update_of_ne h560,Function.update_of_ne h561] using hv k hk

theorem storedEntry_values {m n : ℕ} (a : CalibrationMatrix.Data m n) (i : Fin n) (v : ℕ → ℕ) :
    storedEntry (values a i v)=entry a (v 551) (v 552) i := by
  simp [storedEntry,values,entry]

#print axioms stored_write_frame
#print axioms entry_width

end Maxwell.Continuum.Calibration.PowerMachine.NormalizedEntry
