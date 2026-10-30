import Maxwell.Continuum.CalibrationNormalizedArrayState

/-! The output traversal count is copied from the actual retained dimension
word. The input arrays, output descriptors, and computed scale survive. -/

namespace Maxwell.Continuum.Calibration.PowerMachine.NormalizedEntry

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open RationalDataflow RationalDataflow.PartArray
open RationalAccumulator (Blank)
set_option maxHeartbeats 2500000

def counterCode : Code := WordReplace.code 107 140

theorem counter_executes {n : ℕ} (a : CalibrationMatrix.Data n n) (b : Table n)
    (v : ℕ → ℕ) (count : List Bool) (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hs : NatAssign.Bank ids v s.val) (ha : CalibrationMatrix.Stored a s.val) (hb : b.OutputReady s)
    (hc : BankArray.Word s.val 107 count) (hz : Blank s.val 140) :
    ∃ t, Executes input tape counterCode (15*count.length+21) s t ∧
      NatAssign.Bank ids v t.val ∧ CalibrationMatrix.Stored a t.val ∧ b.OutputReady t ∧
      BankArray.Word t.val 140 count ∧ WordReplace.Frame 140 s.val t.val := by
  obtain ⟨t,he,word,frame⟩ := WordReplace.executes 107 140 (by decide)
    input tape count [] s hc ((RationalAccumulator.zero_word_iff_blank _ _).mpr hz)
  have keep (i : ℕ) (hi : i≠140) := frame.2.2.2.2.2.1 i hi
  have bank : NatAssign.Bank ids v t.val := by
    intro i hi
    have hn : i≠140 := by
      simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hi
      omega
    exact RationalAccumulator.word_of_eq (keep i hn) (hs i hi)
  have stored : CalibrationMatrix.Stored a t.val :=
    ⟨BankArray.word_of_eq (keep 100 (by decide)) ha.width,
      BankArray.word_of_eq (keep 101 (by decide)) ha.clock,
      BankArray.word_of_eq (keep 110 (by decide)) ha.matrixPositiveBase,
      BankArray.word_of_eq (keep 111 (by decide)) ha.matrixNegativeBase,
      BankArray.word_of_eq (keep 112 (by decide)) ha.vectorPositiveBase,
      BankArray.word_of_eq (keep 113 (by decide)) ha.vectorNegativeBase,
      by simpa only [frame.2.2.1] using ha.matrixPositive,
      by simpa only [frame.2.2.1] using ha.matrixNegative,
      by simpa only [frame.2.2.1] using ha.vectorPositive,
      by simpa only [frame.2.2.1] using ha.vectorNegative⟩
  have scratch : BankArray.Scratch t.val := by
    rcases hb.scratch with ⟨h0,h1,h2,h3,h5,h6,h8,h9⟩
    exact ⟨RationalAccumulator.blank_of_eq (keep 0 (by decide)) h0,
      RationalAccumulator.blank_of_eq (keep 1 (by decide)) h1,
      RationalAccumulator.blank_of_eq (keep 2 (by decide)) h2,
      RationalAccumulator.blank_of_eq (keep 3 (by decide)) h3,
      RationalAccumulator.blank_of_eq (keep 5 (by decide)) h5,
      RationalAccumulator.blank_of_eq (keep 6 (by decide)) h6,
      RationalAccumulator.blank_of_eq (keep 8 (by decide)) h8,
      RationalAccumulator.blank_of_eq (keep 9 (by decide)) h9⟩
  have output : b.OutputReady t := by
    apply hb.transfer frame.2.2.1 _ scratch (RationalAccumulator.blank_of_eq (keep 7 (by decide)) hb.seven)
    intro i hi
    apply keep i
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    omega
  exact ⟨t,by simpa only [counterCode,List.length_nil,Nat.mul_zero,Nat.zero_add] using he,
    bank,stored,output,word,frame⟩

#print axioms counter_executes

end Maxwell.Continuum.Calibration.PowerMachine.NormalizedEntry
