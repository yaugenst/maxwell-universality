import Maxwell.Continuum.RationalDataflowArrayRead

/-! A uniform three-channel rational array, read into the existing shared register bank. -/

namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

theorem ids_ge_ten (S : Finset ℕ) (i : ℕ) (hi : i∈ids S) : 10 ≤ i := by
  rcases Finset.mem_union.mp hi with hp | hw
  · obtain ⟨r,_,hr⟩ := Finset.mem_biUnion.mp hp
    simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at hr
    rcases hr with rfl | rfl | rfl
    · exact (by omega : 10 ≤ 1000).trans (positivePort_ge r)
    · exact (by omega : 10 ≤ 1000).trans (negativePort_ge r)
    · exact (by omega : 10 ≤ 1000).trans (denominatorPort_ge r)
  · simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton] at hw
    omega

namespace PartArray

/-- Runtime metadata and the literal equal-width memory words of the three channels. -/
structure Table (n : ℕ) where
  width : List Bool
  basePositive : List Bool
  baseNegative : List Bool
  baseDenominator : List Bool
  clock : List Bool
  positive : Vector (List Bool) n
  negative : Vector (List Bool) n
  denominator : Vector (List Bool) n
  width_pos : 0<width.length
  clock_length : clock.length=addressValue width

def Table.get {n : ℕ} (a : Table n) (i : Fin n) : Parts :=
  ⟨addressValue (a.positive.get i),addressValue (a.negative.get i),addressValue (a.denominator.get i)⟩

/-- The index is deliberately absent: tape 201 may be the runtime countdown itself. -/
structure Table.Ready {n : ℕ} (a : Table n) (s : Store) : Prop where
  scratch : BankArray.Scratch s.val
  seven : RationalAccumulator.Blank s.val 7
  width : BankArray.Word s.val 200 a.width
  basePositive : BankArray.Word s.val 202 a.basePositive
  baseNegative : BankArray.Word s.val 203 a.baseNegative
  baseDenominator : BankArray.Word s.val 204 a.baseDenominator
  clock : BankArray.Word s.val 205 a.clock
  positive : BitArray.Represents s.val.memory (addressValue a.basePositive) (addressValue a.width) a.positive
  negative : BitArray.Represents s.val.memory (addressValue a.baseNegative) (addressValue a.width) a.negative
  denominator : BitArray.Represents s.val.memory (addressValue a.baseDenominator) (addressValue a.width) a.denominator

theorem Table.Ready.read_frame {n : ℕ} {a : Table n} {s t : Store} {target : ℕ}
    (h : a.Ready s) (ht : 1000≤target) (f : ArrayRead.Frame target s.val t.val)
    (hz : BankArray.Scratch t.val) (h7 : RationalAccumulator.Blank t.val 7) : a.Ready t := by
  refine ⟨hz,h7,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact BankArray.word_of_eq (f.tapes 200 (by decide) (by omega)) h.width
  · exact BankArray.word_of_eq (f.tapes 202 (by decide) (by omega)) h.basePositive
  · exact BankArray.word_of_eq (f.tapes 203 (by decide) (by omega)) h.baseNegative
  · exact BankArray.word_of_eq (f.tapes 204 (by decide) (by omega)) h.baseDenominator
  · exact BankArray.word_of_eq (f.tapes 205 (by decide) (by omega)) h.clock
  · simpa only [f.memory] using h.positive
  · simpa only [f.memory] using h.negative
  · simpa only [f.memory] using h.denominator

def readCode (target : ℕ) : Code :=
  .seq (ArrayRead.code 200 201 202 205 (positivePort target))
    (.seq (ArrayRead.code 200 201 203 205 (negativePort target))
      (ArrayRead.code 200 201 204 205 (denominatorPort target)))

def Table.readCost {n : ℕ} (a : Table n) (index : List Bool) (old : Parts) : ℕ :=
  6*(old.positive.bits.length+old.negative.bits.length+old.denominator.bits.length)+
  BankArray.costCap a.width index a.basePositive a.clock+
  BankArray.costCap a.width index a.baseNegative a.clock+
  BankArray.costCap a.width index a.baseDenominator a.clock+96*addressValue a.width+138

structure Frame (target : ℕ) (s t : BitRAMState) : Prop where
  memory : t.memory=s.memory
  inputHead : t.inputHead=s.inputHead
  randomCursor : t.randomCursor=s.randomCursor
  output : t.output=s.output
  tapes : ∀ i, 10 ≤ i → i∉cellPorts target → t.tapes i=s.tapes i

theorem read_executes {n : ℕ} (a : Table n) (S : Finset ℕ) (target : ℕ) (ht : target∈S)
    (v : ℕ→Parts) (input : List Bool) (tape : ℕ→Bool) (index : List Bool) (i : Fin n)
    (hindex : addressValue index=i.val) (s : Store) (hs : RationalDataflow.Ready S v s)
    (ha : a.Ready s) (hi : BankArray.Word s.val 201 index) :
    ∃ cost t, Executes input tape (readCode target) cost s t ∧ cost≤a.readCost index (v target) ∧
      RationalDataflow.Ready S (Function.update v target (a.get i)) t ∧ a.Ready t ∧
      BankArray.Word t.val 201 index ∧ Frame target s.val t.val := by
  have hp := positivePort_ge target
  have hn := negativePort_ge target
  have hd := denominatorPort_ge target
  have pm : positivePort target∈ids S := cell_mem ht (by simp [cellPorts])
  have nm : negativePort target∈ids S := cell_mem ht (by simp [cellPorts])
  have dm : denominatorPort target∈ids S := cell_mem ht (by simp [cellPorts])
  obtain ⟨c1,t1,e1,h1,b1,z1,s1,_,f1⟩ := ArrayRead.executes (ids S) (ids_ge_ten S)
    200 201 202 205 (positivePort target) (by decide) (by decide) (by decide) (by decide) pm
    (by omega) (by omega) (by omega) (by omega) input tape a.width index a.basePositive a.clock
    a.positive i a.width_pos hindex a.clock_length (dataValues v) s hs.1 ha.scratch ha.seven
    ha.width hi ha.basePositive ha.clock ha.positive
  have a1 := ha.read_frame hp f1 z1 s1
  have i1 := BankArray.word_of_eq (f1.tapes 201 (by decide) (by omega)) hi
  obtain ⟨c2,t2,e2,h2,b2,z2,s2,_,f2⟩ := ArrayRead.executes (ids S) (ids_ge_ten S)
    200 201 203 205 (negativePort target) (by decide) (by decide) (by decide) (by decide) nm
    (by omega) (by omega) (by omega) (by omega) input tape a.width index a.baseNegative a.clock
    a.negative i a.width_pos hindex a.clock_length _ t1 b1 a1.scratch a1.seven
    a1.width i1 a1.baseNegative a1.clock a1.negative
  have a2 := a1.read_frame hn f2 z2 s2
  have i2 := BankArray.word_of_eq (f2.tapes 201 (by decide) (by omega)) i1
  obtain ⟨c3,t3,e3,h3,b3,z3,s3,_,f3⟩ := ArrayRead.executes (ids S) (ids_ge_ten S)
    200 201 204 205 (denominatorPort target) (by decide) (by decide) (by decide) (by decide) dm
    (by omega) (by omega) (by omega) (by omega) input tape a.width index a.baseDenominator a.clock
    a.denominator i a.width_pos hindex a.clock_length _ t2 b2 a2.scratch a2.seven
    a2.width i2 a2.baseDenominator a2.clock a2.denominator
  refine ⟨c1+(c2+c3),t3,e1.seq (e2.seq e3),?_,?_,a2.read_frame hd f3 z3 s3,
    BankArray.word_of_eq (f3.tapes 201 (by decide) (by omega)) i2,?_⟩
  · simp at h1 h2 h3
    unfold Table.readCost
    omega
  · constructor
    · change NatAssign.Bank (ids S) (writeParts (dataValues v) target (a.get i)) t3.val at b3
      rwa [writeParts_dataValues] at b3
    · intro k hk
      interval_cases k
      · exact z3.1
      · exact z3.2.1
      · exact z3.2.2.1
      · exact z3.2.2.2.1
  · refine ⟨f3.memory.trans (f2.memory.trans f1.memory),
      f3.inputHead.trans (f2.inputHead.trans f1.inputHead),
      f3.randomCursor.trans (f2.randomCursor.trans f1.randomCursor),
      f3.output.trans (f2.output.trans f1.output),?_⟩
    intro k hk hkt
    have kp : k≠positivePort target := by intro he; exact hkt (by simp [cellPorts,he])
    have kn : k≠negativePort target := by intro he; exact hkt (by simp [cellPorts,he])
    have kd : k≠denominatorPort target := by intro he; exact hkt (by simp [cellPorts,he])
    exact (f3.tapes k hk kd).trans ((f2.tapes k hk kn).trans (f1.tapes k hk kp))

#print axioms read_executes

end PartArray
end Maxwell.Continuum.RationalDataflow
