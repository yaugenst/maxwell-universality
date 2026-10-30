import Maxwell.Continuum.CalibrationInverseDenominatorPower
import Maxwell.Continuum.CalibrationPowerInitialized

/-! The denominator exponent is evaluated from the retained runtime words
without disturbing either parity of the current power buffer. -/

namespace Maxwell.Continuum.Calibration.PowerMachine

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open RationalAccumulator (Word Blank)
namespace Denominator
set_option maxHeartbeats 2800000
set_option maxRecDepth 16384

theorem ready_preserved {n B : ℕ} {b : Buffers n} {count : List Bool} {s t : BitRAMState}
    (hb : b.Ready count B s) (f : BinaryPrecision.Frame NeumannMachine.DenominatorPower.changed s t)
    (hz : NatAssign.Scratch t) : b.Ready count B t := by
  obtain ⟨vi,hvi,hvl,cal,stored,indices,out,countWord,blank,h37,h108,h109⟩ := hb
  have keep (i : ℕ) (hi : 4 ≤ i) (hbig : i < 530) : t.tapes i=s.tapes i :=
    f.tapes i (by simp only [NeumannMachine.DenominatorPower.changed,
      Finset.mem_insert,Finset.mem_singleton]; omega)
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

def loadedValues (D N : ℕ) (i : ℕ) : ℕ := if i=126 then D else if i=304 then N else 0

theorem from_buffer {n : ℕ} (b : Buffers n) (D N B : ℕ) (count : List Bool)
    (hB : 1≤B) (hD : D.bits.length≤B) (hN : N.bits.length≤B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hb : b.Ready count B s.val) (hden : Word s.val 126 D) (hcount : Word s.val 304 N)
    (hfresh : ∀ i∈Finset.Icc 530 534, Blank s.val i) :
    ∃ cost t, Executes input tape NeumannMachine.DenominatorPower.code cost s t ∧
      cost≤2^36*(N+2)^3*(B+2)^2 ∧
      Word t.val 532 (D^(N+1)) ∧ Word t.val 533 1 ∧
      Word t.val 530 D ∧ Word t.val 531 1 ∧ Blank t.val 534 ∧
      b.Ready count B t.val ∧ BinaryPrecision.Frame NeumannMachine.DenominatorPower.changed s.val t.val := by
  have bank : NatAssign.Bank NeumannMachine.DenominatorPower.ids (loadedValues D N) s.val := by
    intro i hi
    simp only [NeumannMachine.DenominatorPower.ids,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · simpa [loadedValues] using hden
    · simpa [loadedValues] using hcount
    all_goals simpa [loadedValues] using
      (RationalAccumulator.zero_word_iff_blank _ _).mpr (hfresh _ (by decide))
  have widths : ∀ i∈NeumannMachine.DenominatorPower.ids, (loadedValues D N i).bits.length≤B := by
    intro i _
    have hz : (0:ℕ).bits.length=0 := rfl
    simp only [loadedValues]
    split_ifs <;> omega
  obtain ⟨vi,hvi,hvl,cal,rest⟩ := hb
  have zero : NatAssign.Scratch s.val := by
    intro i hi
    interval_cases i
    · exact cal.2.1.1
    · exact cal.2.1.2.1
    · exact cal.2.1.2.2.1
    · exact cal.2.1.2.2.2.1
  obtain ⟨cost,t,run,hcost,power,one,base,unit,blank,scratch,frame⟩ :=
    NeumannMachine.DenominatorPower.executes (loadedValues D N) B hB widths input tape s bank zero
  have h126 : loadedValues D N 126=D := by simp [loadedValues]
  have h304 : loadedValues D N 304=N := by simp [loadedValues]
  rw [h126,h304] at power
  rw [h126] at base
  rw [h304] at hcost
  exact ⟨cost,t,run,hcost.trans (NeumannMachine.DenominatorPower.costBound_polynomial N B),
    power,one,base,unit,blank,ready_preserved ⟨vi,hvi,hvl,cal,rest⟩ frame scratch,frame⟩

#print axioms from_buffer

end Denominator
end Maxwell.Continuum.Calibration.PowerMachine
