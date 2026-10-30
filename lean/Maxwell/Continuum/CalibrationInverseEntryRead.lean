import Maxwell.Continuum.CalibrationInverseDenominatorPower
import Maxwell.Continuum.RationalDataflowArrayCost
import Maxwell.Cost.CalibrationMatrix.Horner.Semantics

/-! Actual indexed reads of the cached inverse numerator. The persistent
integer-array descriptors are used directly, and the computed common
denominator is copied from its runtime power register. -/

namespace Maxwell.Continuum.Calibration.NeumannMachine.OutputRead

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open Maxwell.Continuum.RationalDataflow
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def ids : Finset ℕ := {30,31,32}
def code : Code := .seq (ArrayRead.code 100 140 112 101 30)
  (.seq (ArrayRead.code 100 140 113 101 31) (WordReplace.code 532 32))

def entryParts {n : ℕ} (a : Snapshot n) (D : ℕ) (i : Fin n) : Parts :=
  ⟨addressValue ((a.words 10).get i),addressValue ((a.words 11).get i),D⟩
def values {n : ℕ} (a : Snapshot n) (D : ℕ) (i : Fin n) (v : ℕ → ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update v 30 (entryParts a D i).positive)
    31 (entryParts a D i).negative) 32 D

structure Frame (s t : BitRAMState) : Prop where
  memory : t.memory=s.memory
  inputHead : t.inputHead=s.inputHead
  randomCursor : t.randomCursor=s.randomCursor
  output : t.output=s.output
  tapes : ∀ k, 10 ≤ k → k∉ids → t.tapes k=s.tapes k

theorem Frame.stored {n : ℕ} {a : Snapshot n} {s t : BitRAMState}
    (f : Frame s t) (h : Horner.Stored a.data a.words s) :
    Horner.Stored a.data a.words t := by
  apply h.of_memory_tapes f.memory
  intro k hk
  simp only [Horner.Metadata] at hk
  apply f.tapes k (by omega)
  simp only [ids,Finset.mem_insert,Finset.mem_singleton]
  omega

theorem Frame.ports {n : ℕ} {a : Snapshot n} {s t : BitRAMState}
    (f : Frame s t) (h : Horner.Ports a.data 10 11 5 4 s) :
    Horner.Ports a.data 10 11 5 4 t :=
  ⟨BankArray.word_of_eq (f.tapes 112 (by decide) (by decide)) h.inputPositive,
   BankArray.word_of_eq (f.tapes 113 (by decide) (by decide)) h.inputNegative,
   BankArray.word_of_eq (f.tapes 114 (by decide) (by decide)) h.outputPositive,
   BankArray.word_of_eq (f.tapes 115 (by decide) (by decide)) h.outputNegative⟩

theorem executes {n : ℕ} (a : Snapshot n) (D B : ℕ) (i : Fin n)
    (hsize : a.data.Sized B) (hD : D.bits.length≤B) (v : ℕ → ℕ)
    (hv : ∀ k∈ids, (v k).bits.length≤B)
    (input : List Bool) (tape : ℕ → Bool) (index : List Bool)
    (hindex : addressValue index=i.val) (hlen : index.length≤B) (s : Store)
    (ha : Horner.Stored a.data a.words s.val) (hp : Horner.Ports a.data 10 11 5 4 s.val)
    (hs : BankArray.Scratch s.val) (h7 : RationalAccumulator.Blank s.val 7)
    (hbank : NatAssign.Bank ids v s.val) (hi : BankArray.Word s.val 140 index)
    (hd : RationalAccumulator.Word s.val 532 D) :
    ∃ cost t, Executes input tape code cost s t ∧ cost≤2^20*(B+5)^2 ∧
      NatAssign.Bank ids (values a D i v) t.val ∧ BankArray.Scratch t.val ∧
      RationalAccumulator.Blank t.val 7 ∧ Horner.Stored a.data a.words t.val ∧
      Horner.Ports a.data 10 11 5 4 t.val ∧ Frame s.val t.val := by
  have allIds : ∀ k∈ids, 10 ≤ k := by
    intro k hk
    simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hk
    omega
  obtain ⟨c0,u0,e0,hc0,bank0,z0,seven0,_,f0⟩ := ArrayRead.executes ids allIds
    100 140 112 101 30 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    input tape a.data.width index (a.data.bases 10) a.data.clock (a.words 10) i
    a.data.width_nonempty hindex a.data.clock_length v s hbank hs h7 ha.width hi hp.inputPositive
    ha.clock (ha.arrays 10)
  obtain ⟨c1,u1,e1,hc1,bank1,z1,seven1,_,f1⟩ := ArrayRead.executes ids allIds
    100 140 113 101 31 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    input tape a.data.width index (a.data.bases 11) a.data.clock (a.words 11) i
    a.data.width_nonempty hindex a.data.clock_length _ u0 bank0 z0 seven0
    (BankArray.word_of_eq (f0.tapes 100 (by decide) (by decide)) ha.width)
    (BankArray.word_of_eq (f0.tapes 140 (by decide) (by decide)) hi)
    (BankArray.word_of_eq (f0.tapes 113 (by decide) (by decide)) hp.inputNegative)
    (BankArray.word_of_eq (f0.tapes 101 (by decide) (by decide)) ha.clock)
    (by simpa only [f0.memory] using ha.arrays 11)
  have den1 := RationalAccumulator.word_of_eq
    ((f1.tapes 532 (by decide) (by decide)).trans (f0.tapes 532 (by decide) (by decide))) hd
  have old32 : RationalAccumulator.Word u1.val 32 (v 32) := by
    simpa only [Function.update_of_ne (by decide : (32:ℕ)≠31),
      Function.update_of_ne (by decide : (32:ℕ)≠30)] using bank1 32 (by decide)
  obtain ⟨t,e2,den2,f2⟩ := WordReplace.executes 532 32 (by decide) input tape D.bits (v 32).bits
    u1 den1 old32
  have frame : Frame s.val t.val := by
    refine ⟨f2.2.2.1.trans (f1.memory.trans f0.memory),
      f2.2.1.trans (f1.inputHead.trans f0.inputHead),
      f2.2.2.2.1.trans (f1.randomCursor.trans f0.randomCursor),
      f2.2.2.2.2.1.trans (f1.output.trans f0.output),?_⟩
    intro k hk hout
    simp only [ids,Finset.mem_insert,Finset.mem_singleton,not_or] at hout
    exact (f2.2.2.2.2.2.1 k hout.2.2).trans
      ((f1.tapes k hk hout.2.1).trans (f0.tapes k hk hout.1))
  have bank : NatAssign.Bank ids (values a D i v) t.val := by
    intro k hk
    by_cases h32 : k=32
    · subst k
      change BankArray.Word t.val 32 D.bits
      exact den2
    · simp only [values,Function.update_of_ne h32]
      exact RationalAccumulator.word_of_eq (f2.2.2.2.2.2.1 k h32) (bank1 k hk)
  have scratch : BankArray.Scratch t.val := by
    rcases z1 with ⟨h0,h1,h2,h3,h5,h6,h8,h9⟩
    exact ⟨RationalAccumulator.blank_of_eq (f2.2.2.2.2.2.1 0 (by decide)) h0,
      RationalAccumulator.blank_of_eq (f2.2.2.2.2.2.1 1 (by decide)) h1,
      RationalAccumulator.blank_of_eq (f2.2.2.2.2.2.1 2 (by decide)) h2,
      RationalAccumulator.blank_of_eq (f2.2.2.2.2.2.1 3 (by decide)) h3,
      RationalAccumulator.blank_of_eq (f2.2.2.2.2.2.1 5 (by decide)) h5,
      RationalAccumulator.blank_of_eq (f2.2.2.2.2.2.1 6 (by decide)) h6,
      RationalAccumulator.blank_of_eq (f2.2.2.2.2.2.1 8 (by decide)) h8,
      RationalAccumulator.blank_of_eq (f2.2.2.2.2.2.1 9 (by decide)) h9⟩
  refine ⟨c0+(c1+(6*(v 32).bits.length+15*D.bits.length+21)),t,e0.seq (e1.seq e2),?_,
    bank,scratch,RationalAccumulator.blank_of_eq (f2.2.2.2.2.2.1 7 (by decide)) seven1,
    frame.stored ha,frame.ports hp,frame⟩
  have clockWidth : a.data.clock.length≤B := by rw [a.data.clock_length]; exact hsize.2.1
  have cap0 := PartArray.bankCost_bound a.data.width index (a.data.bases 10) a.data.clock B
    hsize.1 hlen (hsize.2.2.2.2.1 10) clockWidth hsize.2.1
  have cap1 := PartArray.bankCost_bound a.data.width index (a.data.bases 11) a.data.clock B
    hsize.1 hlen (hsize.2.2.2.2.1 11) clockWidth hsize.2.1
  simp only [Function.update_of_ne (by decide : (31:ℕ)≠30)] at hc1
  have w30 := hv 30 (by decide)
  have w31 := hv 31 (by decide)
  have w32 := hv 32 (by decide)
  nlinarith only [hc0,hc1,cap0,cap1,w30,w31,w32,hD,hsize.2.1]

theorem entryParts_value {n : ℕ} (a : Snapshot n) (D : ℕ) (i : Fin n) :
    (entryParts a D i).value=((Horner.channels a.words 10 11).value i:ℚ)/(D:ℚ) := by
  simp [entryParts,Parts.value,Horner.channels,Channels.value]

#print axioms executes
#print axioms entryParts_value

end Maxwell.Continuum.Calibration.NeumannMachine.OutputRead
