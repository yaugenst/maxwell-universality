import Maxwell.Continuum.WellStrengthTableSetupMeasure

namespace Maxwell.Continuum.WellStrengthInitialization.Table
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
open RationalAccumulator (Blank Word)
set_option maxHeartbeats 4500000
set_option maxRecDepth 16384

namespace Allocation
abbrev clearHeaders := Calibration.PowerMachine.BufferNorm.Allocation.clearHeaders
abbrev changed := Calibration.PowerMachine.BufferNorm.Allocation.changed
abbrev code := Calibration.PowerMachine.BufferNorm.Allocation.code
end Allocation

def code : Code := .seq measureCode Allocation.code
def work : Finset ℕ := changed∪Allocation.changed
def metadataBudget (v : ℕ→ℕ) : ℕ := slotWidth v+(v 2600).bits.length+(v 1209).bits.length+
  (slotWidth v).bits.length+4
def table (v : ℕ→ℕ) (memory : ℕ→Bool) : PartArray.Table (v 1209) :=
  Profile.Runtime.memoryTable (v 1209) (slotWidth v) (v 2600) (slot_positive v) memory
def costBound (v : ℕ→ℕ) (B H : ℕ) : ℕ := measureBound B H+
  2^60*(2^11*(scanWidth B+1)+H+slotWidth v+3)^2

theorem metadata (v : ℕ→ℕ) (memory : ℕ→Bool) : (table v memory).MetadataWidth (metadataBudget v):=by
  apply Profile.Runtime.memoryTable_metadata
  · unfold metadataBudget;omega
  · unfold metadataBudget;omega

theorem executes (v : ℕ→ℕ) (B H : ℕ) (hB : 21≤B)
    (width : ∀i∈sources,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank sources.toFinset v s.val) (scratch : BankArray.Scratch s.val)
    (seven : Blank s.val 7) (thirtySeven : Blank s.val 37) (temp : Blank s.val 216)
    (old : WordCleanup.Bounded clearHeaders H s.val)
    (oldAllocation : WordCleanup.Bounded Allocation.clearHeaders H s.val) :
    ∃cost t,Executes input tape code cost s t ∧ cost≤costBound v B H ∧
      (table v s.val.memory).OutputReady t ∧
      NatAssign.Bank sources.toFinset v t.val ∧ Blank t.val 216 ∧
      BinaryPrecision.Frame work s.val t.val:=by
  have scratch0 : NatAssign.Scratch s.val:=by
    intro i hi
    interval_cases i
    · exact scratch.1
    · exact scratch.2.1
    · exact scratch.2.2.1
    · exact scratch.2.2.2.1
  obtain ⟨c0,a,e0,h0,ba,wa,za,f0⟩:=measure_executes v B H hB width input tape s bank scratch0 old
  have scratchA : BankArray.Scratch a.val:=
    ⟨za 0 (by decide),za 1 (by decide),za 2 (by decide),za 3 (by decide),
      RationalAccumulator.blank_of_eq (f0.tapes 5 (by decide)) scratch.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (f0.tapes 6 (by decide)) scratch.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (f0.tapes 8 (by decide)) scratch.2.2.2.2.2.2.1,
      RationalAccumulator.blank_of_eq (f0.tapes 9 (by decide)) scratch.2.2.2.2.2.2.2⟩
  have allocSubset : Calibration.PowerMachine.BufferNorm.Allocation.inputs⊆ids:=by decide
  have oldA : WordCleanup.Bounded Allocation.clearHeaders H a.val:=by
    intro i hi
    obtain ⟨xs,hxs,word⟩:=oldAllocation i hi
    refine ⟨xs,hxs,BankArray.word_of_eq (f0.tapes i ?_) word⟩
    simp only [Allocation.clearHeaders,Calibration.PowerMachine.BufferNorm.Allocation.clearHeaders,
      List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl <;> decide
  obtain ⟨c1,t,e1,h1,target,_,zt,f1⟩:=Calibration.PowerMachine.BufferNorm.Allocation.executes
    (values v) (2^11*(scanWidth B+1)) H (by rw [(outputs v).2.2.1];exact slot_positive v)
    (fun i hi=>wa i (allocSubset hi)) input tape a (fun i hi=>ba i (allocSubset hi)) scratchA
    (RationalAccumulator.blank_of_eq (f0.tapes 7 (by decide)) seven)
    (RationalAccumulator.blank_of_eq (f0.tapes 37 (by decide)) thirtySeven)
    (RationalAccumulator.blank_of_eq (f0.tapes 216 (by decide)) temp) oldA
  have frame : BinaryPrecision.Frame work s.val t.val:=
    (f0.mono Finset.subset_union_left).trans (f1.mono Finset.subset_union_right)
  refine ⟨c0+c1,t,e0.seq e1,?_,?_,?_,zt,frame⟩
  · rw [(outputs v).2.2.1] at h1
    unfold costBound
    omega
  · simp only [(outputs v).2.2.1,(outputs v).2.2.2.1,f0.memory] at target
    exact target
  · intro i hi
    have hs : i∈sources:=by simpa only [List.mem_toFinset] using hi
    have keep : i∉Allocation.changed:=by
      have disjoint : Disjoint sources.toFinset Allocation.changed:=by decide
      exact Finset.disjoint_left.mp disjoint hi
    apply RationalAccumulator.word_of_eq (f1.tapes i keep)
    simpa only [source_kept v i hs] using ba i (Finset.mem_union_left _ hi)

#print axioms executes
end Maxwell.Continuum.WellStrengthInitialization.Table
