import Maxwell.Continuum.CalibrationBufferNormData
import Maxwell.Continuum.RationalDataflowArrayCost

/-! Normalized coordinates are read from the current integer buffer and
scaled directly. Its live array descriptors do not enter the rational
arithmetic workspace. -/

namespace Maxwell.Continuum.Calibration.PowerMachine.NormalizedEntry

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open RationalDataflow
open RationalAccumulator (Word Blank)
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

def ids : Finset ℕ := {551,552,560,561}
def plan : List NatAssign.Instruction := [.multiply 551 560,.multiply 551 561]
def code : Code := .seq (ArrayRead.code 100 140 112 101 560)
  (.seq (ArrayRead.code 100 140 113 101 561) (NatAssign.code plan))

def entry {m n : ℕ} (a : CalibrationMatrix.Data m n) (scale denominator : ℕ) (i : Fin n) : Parts :=
  ⟨scale*addressValue (a.vectorPositive.get i),scale*addressValue (a.vectorNegative.get i),denominator⟩

def readValues {m n : ℕ} (a : CalibrationMatrix.Data m n) (i : Fin n) (v : ℕ → ℕ) : ℕ → ℕ :=
  Function.update (Function.update v 560 (addressValue (a.vectorPositive.get i)))
    561 (addressValue (a.vectorNegative.get i))

def values {m n : ℕ} (a : CalibrationMatrix.Data m n) (i : Fin n) (v : ℕ → ℕ) : ℕ → ℕ :=
  Function.update (Function.update v 560 (entry a (v 551) (v 552) i).positive)
    561 (entry a (v 551) (v 552) i).negative

structure Frame (s t : BitRAMState) : Prop where
  memory : t.memory=s.memory
  inputHead : t.inputHead=s.inputHead
  randomCursor : t.randomCursor=s.randomCursor
  output : t.output=s.output
  tapes : ∀ k, 10 ≤ k → k≠560 → k≠561 → t.tapes k=s.tapes k

theorem Frame.stored {m n : ℕ} {a : CalibrationMatrix.Data m n} {s t : BitRAMState}
    (f : Frame s t) (h : CalibrationMatrix.Stored a s) : CalibrationMatrix.Stored a t :=
  ⟨BankArray.word_of_eq (f.tapes 100 (by decide) (by decide) (by decide)) h.width,
    BankArray.word_of_eq (f.tapes 101 (by decide) (by decide) (by decide)) h.clock,
    BankArray.word_of_eq (f.tapes 110 (by decide) (by decide) (by decide)) h.matrixPositiveBase,
    BankArray.word_of_eq (f.tapes 111 (by decide) (by decide) (by decide)) h.matrixNegativeBase,
    BankArray.word_of_eq (f.tapes 112 (by decide) (by decide) (by decide)) h.vectorPositiveBase,
    BankArray.word_of_eq (f.tapes 113 (by decide) (by decide) (by decide)) h.vectorNegativeBase,
    by simpa only [f.memory] using h.matrixPositive,
    by simpa only [f.memory] using h.matrixNegative,
    by simpa only [f.memory] using h.vectorPositive,
    by simpa only [f.memory] using h.vectorNegative⟩

theorem plan_values {m n : ℕ} (a : CalibrationMatrix.Data m n) (i : Fin n) (v : ℕ → ℕ) :
    NatAssign.values plan (readValues a i v)=values a i v := by
  ext k
  by_cases h560 : k=560
  · subst k
    simp [plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,readValues,values,entry]
  by_cases h561 : k=561
  · subst k
    simp [plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,readValues,values,entry]
  simp [plan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
    NatAssign.Instruction.target,readValues,values,h560,h561]

theorem executes {m n : ℕ} (a : CalibrationMatrix.Data m n) (B : ℕ) (i : Fin n)
    (hsize : a.Sized B) (v : ℕ → ℕ) (hv : ∀ k∈ids, (v k).bits.length≤B)
    (input : List Bool) (tape : ℕ → Bool) (index : List Bool)
    (hindex : addressValue index=i.val) (hlen : index.length≤B) (s : Store)
    (ha : CalibrationMatrix.Stored a s.val) (hs : BankArray.Scratch s.val) (h7 : Blank s.val 7)
    (hbank : NatAssign.Bank ids v s.val) (hi : BankArray.Word s.val 140 index) :
    ∃ cost t, Executes input tape code cost s t ∧ cost≤2^24*(B+5)^2 ∧
      NatAssign.Bank ids (values a i v) t.val ∧ BankArray.Scratch t.val ∧ Blank t.val 7 ∧
      CalibrationMatrix.Stored a t.val ∧ Frame s.val t.val := by
  have allIds : ∀ k∈ids, 10 ≤ k := by
    intro k hk
    simp only [ids,Finset.mem_insert,Finset.mem_singleton] at hk
    omega
  obtain ⟨c0,u0,e0,hc0,b0,z0,seven0,_,f0⟩ := ArrayRead.executes ids allIds
    100 140 112 101 560 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    input tape a.width index a.vectorPositiveBase a.clock a.vectorPositive i
    a.width_nonempty hindex a.clock_length v s hbank hs h7 ha.width hi ha.vectorPositiveBase
    ha.clock ha.vectorPositive
  obtain ⟨c1,u1,e1,hc1,b1,z1,seven1,_,f1⟩ := ArrayRead.executes ids allIds
    100 140 113 101 561 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    input tape a.width index a.vectorNegativeBase a.clock a.vectorNegative i
    a.width_nonempty hindex a.clock_length _ u0 b0 z0 seven0
    (BankArray.word_of_eq (f0.tapes 100 (by decide) (by decide)) ha.width)
    (BankArray.word_of_eq (f0.tapes 140 (by decide) (by decide)) hi)
    (BankArray.word_of_eq (f0.tapes 113 (by decide) (by decide)) ha.vectorNegativeBase)
    (BankArray.word_of_eq (f0.tapes 101 (by decide) (by decide)) ha.clock)
    (by simpa only [f0.memory] using ha.vectorNegative)
  have rawWidths : ∀ k∈ids, (readValues a i v k).bits.length≤B := by
    intro k hk
    by_cases h560 : k=560
    · subst k
      simp only [readValues,Function.update_of_ne (by decide : (560:ℕ)≠561),Function.update_self]
      exact (canonical_length_le _).trans ((ha.vectorPositive.length i).le.trans hsize.2.1)
    by_cases h561 : k=561
    · subst k
      simp only [readValues,Function.update_self]
      exact (canonical_length_le _).trans ((ha.vectorNegative.length i).le.trans hsize.2.1)
    simpa only [readValues,Function.update_of_ne h560,Function.update_of_ne h561] using hv k hk
  have natScratch : NatAssign.Scratch u1.val := by
    intro k hk
    interval_cases k
    · exact z1.1
    · exact z1.2.1
    · exact z1.2.2.1
    · exact z1.2.2.2.1
  have valid : ∀ a∈plan, a.Valid ids := by simp [plan,NatAssign.Instruction.Valid,ids]
  obtain ⟨c2,t,e2,hc2,b2,z2,f2⟩ := NatAssign.executes ids
    (fun k hk => (by decide : 4≤10).trans (allIds k hk)) plan valid
    (readValues a i v) input tape u1 b1 natScratch
  rw [plan_values] at b2
  have frame : Frame s.val t.val := by
    refine ⟨f2.memory.trans (f1.memory.trans f0.memory),
      f2.inputHead.trans (f1.inputHead.trans f0.inputHead),
      f2.randomCursor.trans (f1.randomCursor.trans f0.randomCursor),
      f2.output.trans (f1.output.trans f0.output),?_⟩
    intro k hk h560 h561
    have out : k∉NatAssign.changes plan := by
      simp [NatAssign.changes,plan,NatAssign.Instruction.target]
      omega
    exact (f2.tapes k out).trans ((f1.tapes k hk h561).trans (f0.tapes k hk h560))
  have keepSmall (k : ℕ) (hk : 4 ≤ k) (hk' : k<10) : t.val.tapes k=u1.val.tapes k := by
    apply f2.tapes k
    simp [NatAssign.changes,plan,NatAssign.Instruction.target]
    omega
  have scratch : BankArray.Scratch t.val :=
    ⟨z2 0 (by decide),z2 1 (by decide),z2 2 (by decide),z2 3 (by decide),
      RationalAccumulator.blank_of_eq (keepSmall 5 (by decide) (by decide)) z1.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keepSmall 6 (by decide) (by decide)) z1.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keepSmall 8 (by decide) (by decide)) z1.2.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (keepSmall 9 (by decide) (by decide)) z1.2.2.2.2.2.2.2⟩
  refine ⟨c0+(c1+c2),t,e0.seq (e1.seq e2),?_,b2,scratch,
    RationalAccumulator.blank_of_eq (keepSmall 7 (by decide) (by decide)) seven1,frame.stored ha,frame⟩
  have clockWidth : a.clock.length≤B := by rw [a.clock_length]; exact hsize.2.1
  have cap0 := PartArray.bankCost_bound a.width index a.vectorPositiveBase a.clock B
    hsize.1 hlen hsize.2.2.2.2.1 clockWidth hsize.2.1
  have cap1 := PartArray.bankCost_bound a.width index a.vectorNegativeBase a.clock B
    hsize.1 hlen hsize.2.2.2.2.2 clockWidth hsize.2.1
  have price := NatAssign.price_bound ids plan valid (readValues a i v) B rawWidths
    (by simp [plan,NatAssign.Instruction.literalWidth])
  have cost2 : c2≤3000*8^2*(B+2)^2 := by
    simpa only [plan,List.length_cons,List.length_nil] using hc2.trans price
  simp only [Function.update_of_ne (by decide : (561:ℕ)≠560)] at hc1
  have w560 := hv 560 (by decide)
  have w561 := hv 561 (by decide)
  nlinarith only [hc0,hc1,cap0,cap1,cost2,w560,w561,hsize.2.1]

theorem entry_value {m n : ℕ} (a : CalibrationMatrix.Data m n) (scale denominator : ℕ) (i : Fin n) :
    (entry a scale denominator i).value=
      ((addressValue (a.vectorPositive.get i):ℚ)-addressValue (a.vectorNegative.get i))*
        ((scale:ℚ)/denominator) := by
  simp only [entry,Parts.value,Nat.cast_mul]
  ring

#print axioms executes
#print axioms entry_value

end Maxwell.Continuum.Calibration.PowerMachine.NormalizedEntry
