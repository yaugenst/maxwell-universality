import Maxwell.Continuum.CalibrationNeumannCopyPlan
import Maxwell.Continuum.RationalDataflowTableHeaderSwap

/-! The destination is allocated by descriptor arithmetic and its width
clock is copied by an executed word operation. Existing arbitrary memory
is used as the initial table contents. -/

namespace Maxwell.Continuum.Calibration.NeumannMachine

open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open Maxwell.Continuum.RationalDataflow
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

theorem CopyPlan.shared_frame {S : Finset ℕ} {v : ℕ → Parts} {s t : Store}
    (h : SharedConversion.Ready S v s)
    (f : BinaryPrecision.Frame (NatAssign.changes CopyPlan.plan) s.val t.val)
    (hz : NatAssign.Scratch t.val) : SharedConversion.Ready S v t := by
  constructor
  · intro i hi
    apply RationalAccumulator.word_of_eq (f.tapes i _) (h.1 i hi)
    intro him
    have hig := SharedConversion.bankIds_ge S i hi
    simp only [NatAssign.changes,CopyPlan.plan,List.map_cons,List.map_nil,
      NatAssign.Instruction.target,List.toFinset_cons,List.toFinset_nil,
      Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false] at him
    have hc : i=305 ∨ i=306 ∨ i=307 ∨ i=210 ∨ i=212 ∨ i=213 ∨ i=214 ∨ i=303 := by omega
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact outside_shared_changed S _ (by decide) (Finset.mem_union_right _ hi)
  · intro i hi
    by_cases hlt : i<4
    · exact hz i hlt
    · have he : i=4 := by omega
      subst i
      exact RationalAccumulator.blank_of_eq (f.tapes 4 (by
        simp [NatAssign.changes,CopyPlan.plan,NatAssign.Instruction.target])) (h.2 4 (by decide))

theorem shared_headerSwap_frame {S : Finset ℕ} {v : ℕ → Parts} {s t : Store}
    (h : SharedConversion.Ready S v s)
    (f : BinaryPrecision.Frame (insert 216 PartArray.headerSlots) s.val t.val) :
    SharedConversion.Ready S v t := by
  constructor
  · intro i hi
    apply RationalAccumulator.word_of_eq (f.tapes i _) (h.1 i hi)
    intro him
    simp only [PartArray.headerSlots,Finset.mem_insert,Finset.mem_singleton] at him
    rcases him with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      exact outside_shared_changed S _ (by decide) (Finset.mem_union_right _ hi)
  · intro i hi
    exact RationalAccumulator.blank_of_eq (f.tapes i (by
      intro him
      have := PartArray.headerSlots_small i him
      omega)) (h.2 i hi)

def copyPrepareCode : Code := .seq CopyPlan.code (WordReplace.code 205 215)
def copyPrepareCost (B sourceWidth oldWidth : ℕ) : ℕ :=
  3000*8^CopyPlan.plan.length*(B+2)^2+6*oldWidth+15*sourceWidth+21

theorem copyPrepare_executes {n m : ℕ} (a : PartArray.Table (tableSize n))
    (old : PartArray.Table m) (heap D N B : ℕ) (hl : SourceLayout a heap)
    (v : ℕ → ℕ) (hi : CopyPlan.Inputs v n (addressValue a.width) heap D N)
    (hbits : ∀ i ∈ CopyPlan.ids, (v i).bits.length ≤ B)
    (S : Finset ℕ) (logical : ℕ → Parts)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (hbank : NatAssign.Bank CopyPlan.ids v s.val)
    (hs : SharedConversion.Ready S logical s) (ha : a.Ready s) (ho : old.OutputReady s) :
    ∃ cost t, Executes input tape copyPrepareCode cost s t ∧
      cost ≤ copyPrepareCost B (addressValue a.width) (addressValue old.width) ∧
      SharedConversion.Ready S logical t ∧ a.Ready t ∧
      (copyTarget a heap s.val.memory).OutputReady t ∧
      NatAssign.Bank Descriptors.ids (NatAssign.values CopyPlan.plan v) t.val ∧
      t.val.tapes 201=s.val.tapes 201 ∧ t.val.memory=s.val.memory := by
  obtain ⟨c,u,he,hc,hb,header,hz,frame⟩ := CopyPlan.executes v n (addressValue a.width)
    heap D N B hi hbits input tape s hbank (fun i hi => hs.2 i (by omega))
  have keep (i : ℕ) (hi : i ∈ ([5,6,7,8,9,37,200,201,202,203,204,205,215] : List ℕ)) :
      u.val.tapes i=s.val.tapes i := by
    apply frame.tapes
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [NatAssign.changes,CopyPlan.plan,NatAssign.Instruction.target]
  have shared := CopyPlan.shared_frame hs frame hz
  have sourceClock := BankArray.word_of_eq (keep 205 (by simp)) ha.clock
  have oldClock := BankArray.word_of_eq (keep 215 (by simp)) ho.clock
  obtain ⟨t,et,clock,ft⟩ := WordReplace.executes 205 215 (by decide) input tape a.clock old.clock
    u sourceClock oldClock
  have tapes := ft.2.2.2.2.2.1
  have memory : t.val.memory=s.val.memory := ft.2.2.1.trans frame.memory
  have scratch : BankArray.Scratch t.val :=
    ⟨RationalAccumulator.blank_of_eq (tapes 0 (by decide)) (hz 0 (by decide)),
     RationalAccumulator.blank_of_eq (tapes 1 (by decide)) (hz 1 (by decide)),
     RationalAccumulator.blank_of_eq (tapes 2 (by decide)) (hz 2 (by decide)),
     RationalAccumulator.blank_of_eq (tapes 3 (by decide)) (hz 3 (by decide)),
     RationalAccumulator.blank_of_eq ((tapes 5 (by decide)).trans (keep 5 (by simp))) ha.scratch.2.2.2.2.1,
     RationalAccumulator.blank_of_eq ((tapes 6 (by decide)).trans (keep 6 (by simp))) ha.scratch.2.2.2.2.2.1,
     RationalAccumulator.blank_of_eq ((tapes 8 (by decide)).trans (keep 8 (by simp))) ha.scratch.2.2.2.2.2.2.1,
     RationalAccumulator.blank_of_eq ((tapes 9 (by decide)).trans (keep 9 (by simp))) ha.scratch.2.2.2.2.2.2.2⟩
  have seven := RationalAccumulator.blank_of_eq ((tapes 7 (by decide)).trans (keep 7 (by simp))) ha.seven
  have source : a.Ready t := by
    refine ⟨scratch,seven,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact BankArray.word_of_eq ((tapes 200 (by decide)).trans (keep 200 (by simp))) ha.width
    · exact BankArray.word_of_eq ((tapes 202 (by decide)).trans (keep 202 (by simp))) ha.basePositive
    · exact BankArray.word_of_eq ((tapes 203 (by decide)).trans (keep 203 (by simp))) ha.baseNegative
    · exact BankArray.word_of_eq ((tapes 204 (by decide)).trans (keep 204 (by simp))) ha.baseDenominator
    · exact BankArray.word_of_eq ((tapes 205 (by decide)).trans (keep 205 (by simp))) ha.clock
    · simpa only [memory] using ha.positive
    · simpa only [memory] using ha.negative
    · simpa only [memory] using ha.denominator
  have target : (copyTarget a heap s.val.memory).OutputReady t := by
    refine ⟨scratch,seven,?_,?_,?_,?_,?_,clock,?_,?_,?_⟩
    · exact RationalAccumulator.blank_of_eq ((tapes 37 (by decide)).trans (keep 37 (by simp))) ho.packing
    · change BankArray.Word t.val 210 a.width
      rw [hl.canonical]
      exact RationalAccumulator.word_of_eq (tapes 210 (by decide)) header.widthWord
    · exact RationalAccumulator.word_of_eq (tapes 212 (by decide)) header.positive
    · exact RationalAccumulator.word_of_eq (tapes 213 (by decide)) header.negative
    · exact RationalAccumulator.word_of_eq (tapes 214 (by decide)) header.denominator
    · simpa only [copyTarget,addressValue_bits,memory] using memoryWords_represents s.val.memory
        (heap+3*tableSize n*addressValue a.width) (addressValue a.width) (tableSize n)
    · simpa only [copyTarget,addressValue_bits,memory] using memoryWords_represents s.val.memory
        (heap+4*tableSize n*addressValue a.width) (addressValue a.width) (tableSize n)
    · simpa only [copyTarget,addressValue_bits,memory] using memoryWords_represents s.val.memory
        (heap+5*tableSize n*addressValue a.width) (addressValue a.width) (tableSize n)
  have state : SharedConversion.Ready S logical t := by
    constructor
    · intro i hi
      apply RationalAccumulator.word_of_eq (tapes i _) (shared.1 i hi)
      intro hh
      subst i
      exact outside_shared_changed S 215 (by decide) (Finset.mem_union_right _ hi)
    · intro i hi
      exact RationalAccumulator.blank_of_eq (tapes i (by omega)) (shared.2 i hi)
  have bank : NatAssign.Bank Descriptors.ids (NatAssign.values CopyPlan.plan v) t.val := by
    intro i hi
    apply RationalAccumulator.word_of_eq (tapes i _) (hb i (Finset.mem_insert_of_mem hi))
    simp only [Descriptors.ids,Finset.mem_union,Finset.mem_Icc,Finset.mem_insert,Finset.mem_singleton] at hi
    omega
  refine ⟨c+(6*old.clock.length+15*a.clock.length+21),t,he.seq et,?_,state,source,target,bank,
    (tapes 201 (by decide)).trans (keep 201 (by simp)),memory⟩
  simp only [copyPrepareCost,old.clock_length,a.clock_length]
  omega

#print axioms copyPrepare_executes

end Maxwell.Continuum.Calibration.NeumannMachine
