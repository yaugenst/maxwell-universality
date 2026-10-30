import Maxwell.Continuum.CalibrationBufferNormalization
import Maxwell.Continuum.CalibrationNormFactor
import Maxwell.Continuum.CalibrationNeumannCopyFrame

/-! One fixed normalization program computes the actual array norm and
retains a single shared scale for all output coordinates. -/

namespace Maxwell.Continuum.Calibration.PowerMachine.BufferNorm

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open RationalAccumulator (Word Blank)
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def scaleCode : Code := .seq normalizationCode Factor.code

def arrayNormRadicand {n : ℕ} (b : Buffers n) (D K P : ℕ) : ℕ :=
  Root.normRadicand (Pairing.positive (bufferChannels b) (bufferChannels b))
    (Pairing.negative (bufferChannels b) (bufferChannels b)) (D^(K+1)) P

def arrayNormCenter {n : ℕ} (b : Buffers n) (D K P : ℕ) : ℚ :=
  sqrtRationalCenter (∑ i, (((bufferChannels b).value i:ℚ)/(D^(K+1):ℕ))^2) P

theorem scale_executes {n : ℕ} (b : Buffers n) (D K P B : ℕ) (count : List Bool)
    (hB : 1≤B) (hDpos : 0<D) (hD : D.bits.length≤B) (hK : K.bits.length≤B)
    (hsize : b.Sized B) (hcount : addressValue count=n) (hcl : count.length≤B)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hb : b.Ready count B s.val) (hden : Word s.val 126 D) (hiterations : Word s.val 304 K)
    (hprecision : Word s.val 544 P)
    (hfresh : ∀ i∈normalizationFresh∪{550,551,552}, Blank s.val i) :
    ∃ cost t, ∃ denominator : ℕ,
      Executes input tape scaleCode cost s t ∧
      cost≤normalizationCost n K P B+
        Factor.costBound (arrayNormRadicand b D K P) denominator (D^(K+1)) ∧
      0<denominator ∧
      denominator.bits.length≤2*normalizationWidth n K P B+2*P+3 ∧
      NatAssign.Bank Factor.ids
        (Factor.outputValues (arrayNormRadicand b D K P) denominator (D^(K+1))) t.val ∧
      (Factor.factor (arrayNormRadicand b D K P) denominator (D^(K+1))).value=
        (arrayNormCenter b D K P)⁻¹/(D^(K+1):ℕ) ∧
      BankArray.Scratch t.val ∧ Blank t.val 7 ∧
      t.val.memory=s.val.memory ∧ CalibrationMatrix.Stored (data b) t.val ∧
      (∀ i, 553 ≤ i → t.val.tapes i=s.val.tapes i) ∧
      (∀ i∈normalizationExternal, t.val.tapes i=s.val.tapes i) := by
  obtain ⟨c0,u,num,den,e0,hc0,wn,wd,hd,value,denWidth,saved,z0,zA,h7,mem,stored,bank,keep,externalKeep⟩ :=
    normalization_executes b D K P B count hB hDpos hD hK hsize hcount hcl input tape s
      hb hden hiterations hprecision (fun i hi => hfresh i (Finset.mem_union_left _ hi))
  let T := arrayNormRadicand b D K P
  change NatAssign.Bank NaturalRoot.fullIds (NaturalRoot.doneValues T) u.val at bank
  have root : Word u.val 32 (Nat.sqrt T) := by
    simpa [NaturalRoot.doneValues,DyadicSqrt.bank] using bank 32 (by decide)
  have hn : num=Nat.sqrt T := by
    simpa only [addressValue_bits] using congrArg addressValue (NeumannMachine.word_unique wn root)
  have factorBank : NatAssign.Bank Factor.ids (Factor.inputValues T den (D^(K+1))) u.val := by
    intro i hi
    by_cases h548 : i=548
    · subst i
      simpa [Factor.inputValues] using wd
    by_cases h549 : i=549
    · subst i
      simpa [Factor.inputValues] using saved
    by_cases hnew : i∈({550,551,552}:Finset ℕ)
    · have high : 550 ≤ i := by
        simp only [Finset.mem_insert,Finset.mem_singleton] at hnew
        omega
      have zero := RationalAccumulator.blank_of_eq (keep i high)
        (hfresh i (Finset.mem_union_right _ hnew))
      have valueZero : Factor.inputValues T den (D^(K+1)) i=0 := by
        simp only [Finset.mem_insert,Finset.mem_singleton] at hnew
        rcases hnew with rfl|rfl|rfl <;>
          simp [Factor.inputValues,NaturalRoot.doneValues,NaturalRoot.powerValues]
      rw [valueZero]
      exact (RationalAccumulator.zero_word_iff_blank _ _).mpr zero
    have hold : i∈NaturalRoot.fullIds := by
      simp only [Factor.ids,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hi
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hnew
      tauto
    simpa only [Factor.inputValues,ite_eq_right h548,ite_eq_right h549] using bank i hold
  obtain ⟨c1,t,e1,hc1,b1,z1,f1⟩ := Factor.executes T den (D^(K+1)) input tape u factorBank z0
  have finalStored : CalibrationMatrix.Stored (data b) t.val :=
    ⟨BankArray.word_of_eq (f1.tapes 100 (by decide)) stored.width,
      BankArray.word_of_eq (f1.tapes 101 (by decide)) stored.clock,
      BankArray.word_of_eq (f1.tapes 110 (by decide)) stored.matrixPositiveBase,
      BankArray.word_of_eq (f1.tapes 111 (by decide)) stored.matrixNegativeBase,
      BankArray.word_of_eq (f1.tapes 112 (by decide)) stored.vectorPositiveBase,
      BankArray.word_of_eq (f1.tapes 113 (by decide)) stored.vectorNegativeBase,
      by simpa only [f1.memory] using stored.matrixPositive,
      by simpa only [f1.memory] using stored.matrixNegative,
      by simpa only [f1.memory] using stored.vectorPositive,
      by simpa only [f1.memory] using stored.vectorNegative⟩
  have scratch : BankArray.Scratch t.val :=
    ⟨z1 0 (by decide),z1 1 (by decide),z1 2 (by decide),z1 3 (by decide),
      RationalAccumulator.blank_of_eq (f1.tapes 5 (by decide)) zA.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (f1.tapes 6 (by decide)) zA.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (f1.tapes 8 (by decide)) zA.2.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (f1.tapes 9 (by decide)) zA.2.2.2.2.2.2.2⟩
  refine ⟨c0+c1,t,den,e0.seq e1,Nat.add_le_add hc0 hc1,hd,denWidth,b1,?_,scratch,
    RationalAccumulator.blank_of_eq (f1.tapes 7 (by decide)) h7,
    f1.memory.trans mem,finalStored,?_,?_⟩
  · rw [Factor.factor_value,←hn,value]
    rfl
  · intro i hi
    have outside : i∉Factor.changed := by
      simp only [Factor.changed,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
        Finset.mem_Icc]
      omega
    exact (f1.tapes i outside).trans (keep i (by omega))
  · intro i hi
    have outside : i∉Factor.changed := by
      simp only [normalizationExternal,Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    exact (f1.tapes i outside).trans (externalKeep i hi)

#print axioms scale_executes

end Maxwell.Continuum.Calibration.PowerMachine.BufferNorm
