import Maxwell.Continuum.CalibrationBufferDenominatorPower
import Maxwell.Continuum.CalibrationBufferNorm
import Maxwell.Continuum.CalibrationNormRootMachine

/-! The exact normalization scalar is computed directly from the final
stored integer power buffer. No norm, denominator power, or reduced
fraction is supplied by an external evaluator. -/

namespace Maxwell.Continuum.Calibration.PowerMachine.BufferNorm

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open RationalAccumulator (Word Blank)
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def normalizationCode : Code := .seq NeumannMachine.DenominatorPower.code (.seq code Root.code)
def normalizationWidth (n K P B : ℕ) : ℕ :=
  NeumannMachine.StoredPairing.workWidth n B+(K+1)*B+P.bits.length+2
def normalizationCost (n K P B : ℕ) : ℕ :=
  2^36*(K+2)^3*(B+2)^2+costBound n B+Root.costBound P (normalizationWidth n K P B)
def normalizationFresh : Finset ℕ := Root.ids\(Finset.Icc 30 36∪{544})
def normalizationExternal : Finset ℕ := {37,107,140,210,212,213,214,215}

theorem normalization_executes {n : ℕ} (b : Buffers n) (D K P B : ℕ) (count : List Bool)
    (hB : 1≤B) (hDpos : 0<D) (hD : D.bits.length≤B) (hK : K.bits.length≤B)
    (hsize : b.Sized B) (hcount : addressValue count=n) (hcl : count.length≤B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hb : b.Ready count B s.val) (hden : Word s.val 126 D) (hiterations : Word s.val 304 K)
    (hprecision : Word s.val 544 P) (hfresh : ∀ i∈normalizationFresh, Blank s.val i) :
    ∃ cost t, ∃ numerator denominator : ℕ,
      Executes input tape normalizationCode cost s t ∧ cost≤normalizationCost n K P B ∧
      Word t.val 32 numerator ∧ Word t.val 548 denominator ∧ 0<denominator ∧
      (numerator:ℚ)/denominator=
        sqrtRationalCenter (∑ i, (((bufferChannels b).value i:ℚ)/(D^(K+1):ℕ))^2) P ∧
      denominator.bits.length≤2*normalizationWidth n K P B+2*P+3 ∧
      Word t.val 549 (D^(K+1)) ∧ NatAssign.Scratch t.val ∧
      BankArray.Scratch t.val ∧ Blank t.val 7 ∧
      t.val.memory=s.val.memory ∧ CalibrationMatrix.Stored (data b) t.val ∧
      NatAssign.Bank NaturalRoot.fullIds (NaturalRoot.doneValues (Root.normRadicand
        (Pairing.positive (bufferChannels b) (bufferChannels b))
        (Pairing.negative (bufferChannels b) (bufferChannels b)) (D^(K+1)) P)) t.val ∧
      (∀ i, 550 ≤ i → t.val.tapes i=s.val.tapes i) ∧
      (∀ i∈normalizationExternal, t.val.tapes i=s.val.tapes i) := by
  have freshPower : ∀ i∈Finset.Icc 530 534, Blank s.val i := by
    intro i hi
    exact hfresh i ((by decide : Finset.Icc 530 534⊆normalizationFresh) hi)
  obtain ⟨c0,u,e0,hc0,power,one,base,unit,blank,b0,f0⟩ :=
    Denominator.from_buffer b D K B count hB hD hK input tape s hb hden hiterations freshPower
  obtain ⟨c1,v,e1,hc1,cal,stored,_,f1⟩ := executes b count hsize hcount hcl input tape u b0
  let p := Pairing.positive (bufferChannels b) (bufferChannels b)
  let m := Pairing.negative (bufferChannels b) (bufferChannels b)
  have keepNorm (i : ℕ) (hi : i∈Root.ids) (hcore : ¬(30 ≤ i ∧ i ≤ 36)) :
      v.val.tapes i=u.val.tapes i := by
    have hlo := hi
    simp only [Root.ids,RationalRoot.Raw.ids,RationalRoot.ids,NaturalRoot.fullIds,NaturalRoot.ids,
      RationalCanonicalBank.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
      Finset.mem_Icc] at hlo
    exact f1.2.2.2.2 i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have bank : NatAssign.Bank Root.ids (Root.inputValues p m (D^(K+1)) D P) v.val := by
    intro i hi
    by_cases hcore : 30 ≤ i ∧ i ≤ 36
    · have hc := cal.1 i hcore.1 hcore.2
      obtain ⟨hlo,hhi⟩ := hcore
      interval_cases i <;> simpa [Root.inputValues,dotValues,p,m] using hc
    by_cases hpower : 530 ≤ i ∧ i ≤ 534
    · obtain ⟨hlo,hhi⟩ := hpower
      interval_cases i
      · simpa [Root.inputValues] using RationalAccumulator.word_of_eq (keepNorm 530 hi hcore) base
      · simpa [Root.inputValues] using RationalAccumulator.word_of_eq (keepNorm 531 hi hcore) unit
      · simpa [Root.inputValues] using RationalAccumulator.word_of_eq (keepNorm 532 hi hcore) power
      · simpa [Root.inputValues] using RationalAccumulator.word_of_eq (keepNorm 533 hi hcore) one
      · simpa [Root.inputValues] using (RationalAccumulator.zero_word_iff_blank _ _).mpr
          (RationalAccumulator.blank_of_eq (keepNorm 534 hi hcore) blank)
    by_cases h544 : i=544
    · subst i
      simpa [Root.inputValues] using RationalAccumulator.word_of_eq
        ((keepNorm 544 hi hcore).trans (f0.tapes 544 (by decide))) hprecision
    have hf : i∈normalizationFresh := by
      simp only [normalizationFresh,Finset.mem_sdiff,Finset.mem_union,Finset.mem_Icc,
        Finset.mem_singleton]
      exact ⟨hi,not_or_intro hcore h544⟩
    have outside : i∉NeumannMachine.DenominatorPower.changed := by
      have hge := Root.ids_ge i hi
      simp only [NeumannMachine.DenominatorPower.changed,Finset.mem_insert,Finset.mem_singleton]
      omega
    have hz := RationalAccumulator.blank_of_eq ((keepNorm i hi hcore).trans (f0.tapes i outside)) (hfresh i hf)
    simpa [Root.inputValues,show i≠30 by omega,show i≠31 by omega,
      show i≠530 by omega,show i≠531 by omega,show i≠532 by omega,show i≠533 by omega,h544]
      using (RationalAccumulator.zero_word_iff_blank _ _).mpr hz
  have widths : (Pairing.positive (bufferChannels b) (bufferChannels b)).bits.length≤
        NeumannMachine.StoredPairing.workWidth n B ∧
      (Pairing.negative (bufferChannels b) (bufferChannels b)).bits.length≤
        NeumannMachine.StoredPairing.workWidth n B := by
    obtain ⟨_,_,_,_,initialStored,_⟩ := hb
    exact represented_width b hsize initialStored
  have powerWidth := NeumannMachine.DenominatorPower.denominator_width D K B hD
  have zero : NatAssign.Scratch v.val := by
    intro i hi
    interval_cases i
    · exact cal.2.1.1
    · exact cal.2.1.2.1
    · exact cal.2.1.2.2.1
    · exact cal.2.1.2.2.2.1
  obtain ⟨c2,t,num,den,e2,hc2,wn,wd,hd,hvalue,denWidth,saved,rootBankOut,z2,f2⟩ := Root.executes
    p m (D^(K+1)) D P (normalizationWidth n K P B) (by positivity)
    (by unfold normalizationWidth p; omega) (by unfold normalizationWidth m; omega)
    (by unfold normalizationWidth; omega) (by unfold normalizationWidth; nlinarith)
    (by unfold normalizationWidth; omega) input tape v bank zero
  have finalStored : CalibrationMatrix.Stored (data b) t.val := by
    exact ⟨BankArray.word_of_eq (f2.tapes 100 (by decide)) stored.width,
      BankArray.word_of_eq (f2.tapes 101 (by decide)) stored.clock,
      BankArray.word_of_eq (f2.tapes 110 (by decide)) stored.matrixPositiveBase,
      BankArray.word_of_eq (f2.tapes 111 (by decide)) stored.matrixNegativeBase,
      BankArray.word_of_eq (f2.tapes 112 (by decide)) stored.vectorPositiveBase,
      BankArray.word_of_eq (f2.tapes 113 (by decide)) stored.vectorNegativeBase,
      by simpa only [f2.memory] using stored.matrixPositive,
      by simpa only [f2.memory] using stored.matrixNegative,
      by simpa only [f2.memory] using stored.vectorPositive,
      by simpa only [f2.memory] using stored.vectorNegative⟩
  have finalScratch : BankArray.Scratch t.val :=
    ⟨z2 0 (by decide),z2 1 (by decide),z2 2 (by decide),z2 3 (by decide),
      RationalAccumulator.blank_of_eq (f2.tapes 5 (by decide)) cal.2.1.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (f2.tapes 6 (by decide)) cal.2.1.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (f2.tapes 8 (by decide)) cal.2.1.2.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (f2.tapes 9 (by decide)) cal.2.1.2.2.2.2.2.2.2⟩
  refine ⟨c0+(c1+c2),t,num,den,e0.seq (e1.seq e2),?_,wn,wd,hd,?_,denWidth,saved,z2,
    finalScratch,RationalAccumulator.blank_of_eq (f2.tapes 7 (by decide)) cal.2.2,
    f2.memory.trans (f1.1.trans f0.memory),finalStored,rootBankOut,?_,?_⟩
  · unfold normalizationCost
    omega
  · exact hvalue.trans (Root.buffer_value b (D^(K+1)) P)
  · intro i hi
    have h2 : i∉Root.changed := by
      simp only [Root.changed,RationalRoot.Raw.changed,RationalRoot.changed,NaturalRoot.changed,
        NaturalRoot.powerChanged,RationalCanonicalBank.changed,RationalCanonicalBank.ids,
        Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc]
      omega
    have h0 : i∉NeumannMachine.DenominatorPower.changed := by
      simp only [NeumannMachine.DenominatorPower.changed,Finset.mem_insert,Finset.mem_singleton]
      omega
    exact (f2.tapes i h2).trans ((f1.2.2.2.2 i (Or.inr (by omega)) (Or.inr (by omega))
      (by omega) (by omega) (by omega) (by omega) (by omega)).trans (f0.tapes i h0))
  · intro i hi
    have hcases := hi
    simp only [normalizationExternal,Finset.mem_insert,Finset.mem_singleton] at hcases
    have h2 : i∉Root.changed := by rcases hcases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    have h0 : i∉NeumannMachine.DenominatorPower.changed := by
      rcases hcases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    exact (f2.tapes i h2).trans ((f1.2.2.2.2 i (Or.inr (by omega)) (Or.inr (by omega))
      (by omega) (by omega) (by omega) (by omega) (by omega)).trans (f0.tapes i h0))

#print axioms normalization_executes

end Maxwell.Continuum.Calibration.PowerMachine.BufferNorm
