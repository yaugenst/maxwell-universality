import Maxwell.Continuum.CalibrationGeneratedInverse
import Maxwell.Continuum.CalibrationInverseDenominatorPower

/-! The inverse result supplies every arithmetic input for its denominator
power. The actual numerator arrays and their runtime descriptors survive
the power computation. -/

namespace Maxwell.Continuum.Calibration.NeumannMachine.DenominatorPower

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

theorem ready_preserved {n B : ℕ} {a : Snapshot n} {count : List Bool} {s t : BitRAMState}
    (ha : a.Ready count B s) (f : BinaryPrecision.Frame changed s t)
    (hz : NatAssign.Scratch t) : a.Ready count B t := by
  obtain ⟨⟨vi,hvi,hvl,cal,indices,h104,h107,h106,h37,h108,h109⟩,stored,ports⟩ := ha
  have scratch : BankArray.Scratch t :=
    ⟨hz 0 (by decide),hz 1 (by decide),hz 2 (by decide),hz 3 (by decide),
      RationalAccumulator.blank_of_eq (f.tapes 5 (by decide)) cal.2.1.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (f.tapes 6 (by decide)) cal.2.1.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (f.tapes 8 (by decide)) cal.2.1.2.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (f.tapes 9 (by decide)) cal.2.1.2.2.2.2.2.2.2⟩
  have bank : RationalAccumulator.Bank t (dotValues 0 0) := by
    intro k hlo hhi
    exact RationalAccumulator.word_of_eq (f.tapes k (by
      simp only [changed,Finset.mem_insert,Finset.mem_singleton]
      omega)) (cal.1 k hlo hhi)
  have port : Horner.Ports a.data 10 11 5 4 t :=
    ⟨BankArray.word_of_eq (f.tapes 112 (by decide)) ports.inputPositive,
      BankArray.word_of_eq (f.tapes 113 (by decide)) ports.inputNegative,
      BankArray.word_of_eq (f.tapes 114 (by decide)) ports.outputPositive,
      BankArray.word_of_eq (f.tapes 115 (by decide)) ports.outputNegative⟩
  exact ⟨⟨vi,hvi,hvl,⟨bank,scratch,RationalAccumulator.blank_of_eq (f.tapes 7 (by decide)) cal.2.2⟩,
      ⟨BankArray.word_of_eq (f.tapes 102 (by decide)) indices.1,
        BankArray.word_of_eq (f.tapes 103 (by decide)) indices.2⟩,
      BankArray.word_of_eq (f.tapes 104 (by decide)) h104,
      BankArray.word_of_eq (f.tapes 107 (by decide)) h107,
      RationalAccumulator.blank_of_eq (f.tapes 106 (by decide)) h106,
      RationalAccumulator.blank_of_eq (f.tapes 37 (by decide)) h37,
      RationalAccumulator.blank_of_eq (f.tapes 108 (by decide)) h108,
      RationalAccumulator.blank_of_eq (f.tapes 109 (by decide)) h109⟩,
    stored_preserved a stored f,port⟩

def loadedValues (D N : ℕ) (k : ℕ) : ℕ := if k=126 then D else if k=304 then N else 0

theorem from_snapshot {n : ℕ} (a : Snapshot n) (D N B : ℕ) (count : List Bool)
    (hsize : a.data.Sized B) (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (ha : a.Ready count B s.val) (hden : Word s.val 126 D) (hcount : Word s.val 304 N)
    (hfresh : ∀ k∈Finset.Icc 530 534, Blank s.val k) :
    ∃ cost t, Executes input tape code cost s t ∧
      cost≤2^36*(N+2)^3*(B+N.bits.length+3)^2 ∧
      Word t.val 532 (D^(N+1)) ∧ Word t.val 533 1 ∧ Blank t.val 534 ∧
      a.Ready count B t.val ∧ BinaryPrecision.Frame changed s.val t.val := by
  have denEq : a.data.K=D := by
    simpa only [addressValue_bits] using congrArg addressValue (word_unique ha.2.1.K hden)
  have denWidth : D.bits.length≤B := by
    rw [←denEq]
    exact hsize.2.2.2.2.2.1
  have bank : NatAssign.Bank ids (loadedValues D N) s.val := by
    intro k hk
    simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hk
    rcases hk with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · simpa only [loadedValues,ite_true] using hden
    · simpa [loadedValues] using hcount
    all_goals
      simpa [loadedValues] using
        (RationalAccumulator.zero_word_iff_blank _ _).mpr (hfresh _ (by decide))
  have widths : ∀ k∈ids, (loadedValues D N k).bits.length≤B+N.bits.length+1 := by
    intro k _
    simp only [loadedValues]
    split_ifs <;> first | omega | simp
  obtain ⟨vi,hvi,hvl,cal,rest⟩ := ha.1
  have scratch : NatAssign.Scratch s.val := by
    intro k hk
    interval_cases k
    · exact cal.2.1.1
    · exact cal.2.1.2.1
    · exact cal.2.1.2.2.1
    · exact cal.2.1.2.2.2.1
  obtain ⟨cost,t,run,hcost,power,one,_,_,blank,zero,frame⟩ := executes (loadedValues D N)
    (B+N.bits.length+1) (by omega) widths input tape s bank scratch
  have raw : loadedValues D N 126=D ∧ loadedValues D N 304=N := by simp [loadedValues]
  rw [raw.1,raw.2] at power
  rw [raw.2] at hcost
  refine ⟨cost,t,run,?_,power,one,blank,ready_preserved ha frame zero,frame⟩
  have bound := costBound_polynomial N (B+N.bits.length+1)
  simpa only [Nat.add_assoc] using hcost.trans bound

#print axioms ready_preserved
#print axioms from_snapshot

end Maxwell.Continuum.Calibration.NeumannMachine.DenominatorPower
