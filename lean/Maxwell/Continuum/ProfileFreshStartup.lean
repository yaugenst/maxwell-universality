import Maxwell.Continuum.ProfileRetainedPayload
import Maxwell.Continuum.RationalDataflowInitialize

/-! The fixed profile entry point installs its two runtime input words and
initializes its rational register bank by charged literal writes. Every
remaining startup tape is a finite fresh-workspace requirement. -/
namespace Maxwell.Continuum.Profile.Runtime
open RationalDataflow Maxwell.Cost Maxwell.Cost.Structured RationalAccumulator
set_option maxHeartbeats 2500000
set_option maxRecDepth 32768

def entryIds : Finset ℕ := {4426,2600,660,705}
def entryPlan : List NatAssign.Instruction := [.copy 4426 660,.copy 2600 705]
def entryValues (N heap i : ℕ) : ℕ := if i=4426 then N else if i=2600 then heap else 0
def freshTapes : Finset ℕ := RationalDataflow.workspace dftRegisters∪dimensionIds∪allocationIds∪
  startupBlanks∪(PhaseMachine.Runtime.ids.erase 652).erase 653∪(GlueMachine.Runtime.ids.erase 640)∪
  DyadicFloor.extraIds∪NaturalQuotient.workPorts∪serializerPorts∪{4,5,6,7,8,9,37,201,205,215,216,700,701,702,703,991}
def freshStartupCode : Code := .seq (NatAssign.code entryPlan) (Initialize.code dftRegisters)
def entryWidth (N heap : ℕ) : ℕ := N.bits.length+heap.bits.length+1
def freshStartupCost (N heap : ℕ) : ℕ := 3000*8^2*(entryWidth N heap+2)^2+Initialize.cost dftRegisters

structure FreshReady (N heap : ℕ) (s : Store) : Prop where
  dimensions : NatAssign.Bank dimensionIds (initialDimensions N) s.val
  allocation : NatAssign.Bank allocationIds (bufferInput N 0 heap) s.val
  blanks : ∀i∈startupBlanks,Blank s.val i
  rational : Ready dftRegisters Initialize.parts s
  saved : StoredParts.Stored 701 ⟨0,0,0⟩ s.val
  inner : BankArray.Word s.val 201 []
  count : BankArray.Word s.val 700 []
  phase : Phase.Runtime.Clean s.val
  glue : Glue.Clean s.val
  floor : DyadicFloor.Clean s.val
  array : BankArray.Scratch s.val
  seven : Blank s.val 7
  thirtySeven : Blank s.val 37
  inputClock : Blank s.val 205
  outputClock : Blank s.val 215
  swap : Blank s.val 216
  serializer : ∀i∈serializerPorts,Blank s.val i
  capture : s.val.tapes 991=BitTape.blank

theorem freshStartup_executes (N heap : ℕ) (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (precision : Word s.val 4426 N) (heapWord : Word s.val 2600 heap)
    (fresh : ∀i∈freshTapes,s.val.tapes i=BitTape.blank) :
    ∃cost t,Executes input tape freshStartupCode cost s t ∧cost ≤ freshStartupCost N heap ∧
      FreshReady N heap t ∧BinaryPrecision.Frame ({0,1,2,3,660,705}∪RationalDataflow.ids dftRegisters) s.val t.val := by
  have blankS (i : ℕ) (hi : i∈freshTapes) : Blank s.val i:=⟨0,by rw [fresh i hi];rfl⟩
  have valid : ∀a∈entryPlan,a.Valid entryIds:=by simp [entryPlan,NatAssign.Instruction.Valid,entryIds]
  have lower : ∀i∈entryIds,4 ≤ i:=by simp only [entryIds,Finset.mem_insert,Finset.mem_singleton];omega
  have widths : ∀i∈entryIds,(entryValues N heap i).bits.length≤entryWidth N heap:=by
    intro i hi
    simp only [entryIds,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl <;> simp [entryValues,entryWidth] <;> omega
  have bank : NatAssign.Bank entryIds (entryValues N heap) s.val:=by
    intro i hi
    simp only [entryIds,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl
    · simpa [entryValues] using precision
    · simpa [entryValues] using heapWord
    · exact (zero_word_iff_blank _ _).mpr (blankS 660 (by decide +kernel))
    · exact (zero_word_iff_blank _ _).mpr (blankS 705 (by decide +kernel))
  have scratch : NatAssign.Scratch s.val:=by
    intro i hi
    apply blankS i
    have low : {0,1,2,3}⊆freshTapes:=by decide +kernel
    apply low
    simp only [Finset.mem_insert,Finset.mem_singleton]
    omega
  obtain ⟨c,a,e,hc,ba,za,f⟩:=NatAssign.executes entryIds lower entryPlan valid (entryValues N heap)
    input tape s bank scratch
  have charge:=hc.trans (NatAssign.price_bound entryIds entryPlan valid _ (entryWidth N heap) widths
    (by simp [entryPlan,NatAssign.Instruction.literalWidth]))
  have entryFrame : BinaryPrecision.Frame {0,1,2,3,660,705} s.val a.val:=f.mono (by decide)
  obtain ⟨d,t,et,hd,ready,ft⟩:=Initialize.executes dftRegisters input tape a
    (fun i hi=>blank_of_eq (entryFrame.tapes i (Finset.disjoint_left.mp (by decide +kernel :
      Disjoint (RationalDataflow.ids dftRegisters) {0,1,2,3,660,705}) hi)) (blankS i (by
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      exact Finset.mem_union_right _ hi))) za
  have frame : BinaryPrecision.Frame ({0,1,2,3,660,705}∪RationalDataflow.ids dftRegisters) s.val t.val:=
    (entryFrame.mono (by simp)).trans (ft.mono (by
      intro i hi
      rcases Finset.mem_union.mp hi with hi|hi
      · exact Finset.mem_union_left _ (by simp only [Finset.mem_insert,Finset.mem_singleton] at hi ⊢;tauto)
      · exact Finset.mem_union_right _ hi))
  have Nword : Word t.val 660 N:=by
    apply word_of_eq (ft.tapes 660 (by decide +kernel))
    have w:=ba 660 (by decide)
    simpa [entryPlan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,entryValues] using w
  have Hword : Word t.val 705 heap:=by
    apply word_of_eq (ft.tapes 705 (by decide +kernel))
    have w:=ba 705 (by decide)
    simpa [entryPlan,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.value,
      NatAssign.Instruction.target,entryValues] using w
  have blanks (i : ℕ) (hi : i∈freshTapes) (small : i<1000) (hN : i≠660) (hH : i≠705) : Blank t.val i:=by
    by_cases low:i<4
    · exact ready.2 i low
    by_cases raw:i∈RationalDataflow.ids dftRegisters
    · apply (zero_word_iff_blank _ _).mp
      simpa only [dataValues,ite_eq_left small] using ready.1 i raw
    · apply blank_of_eq (frame.tapes i ?_) (blankS i hi)
      intro member
      rcases Finset.mem_union.mp member with small | member
      · simp only [Finset.mem_insert,Finset.mem_singleton] at small
        omega
      · exact raw member
  refine ⟨c+d,t,e.seq et,Nat.add_le_add charge hd,?_,frame⟩
  refine ⟨?_,?_,?_,ready,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i hi
    by_cases he:i=660
    · subst i;exact Nword
    · rw [initialDimensions,ite_eq_right he]
      exact (zero_word_iff_blank _ _).mpr (blanks i (by
        exact (by decide +kernel : dimensionIds⊆freshTapes) hi)
        ((by decide +kernel : ∀i∈dimensionIds,i<1000) i hi) he
        (by intro he;subst i;exact (by decide : 705∉dimensionIds) hi))
  · intro i hi
    by_cases hn:i=660
    · subst i;exact Nword
    by_cases hh:i=705
    · subst i;exact Hword
    have eq : bufferInput N 0 heap i=0:=by simp [bufferInput,hn,hh]
    rw [eq]
    exact (zero_word_iff_blank _ _).mpr (blanks i ((by decide +kernel : allocationIds⊆freshTapes) hi)
      ((by decide +kernel : ∀i∈allocationIds,i<1000) i hi) hn hh)
  · intro i hi
    exact blanks i ((by decide +kernel : startupBlanks⊆freshTapes) hi)
      ((by decide +kernel : ∀i∈startupBlanks,i<1000) i hi)
      (by intro he;subst i;exact (by decide : 660∉startupBlanks) hi)
      (by intro he;subst i;exact (by decide : 705∉startupBlanks) hi)
  · apply StoredParts.Stored.blank
    intro i hi
    have cases : i=701 ∨i=702 ∨i=703:=by simpa [StoredParts.ports] using hi
    rcases cases with rfl|rfl|rfl <;> exact blanks _ (by decide +kernel) (by decide) (by decide) (by decide)
  · exact (zero_word_iff_blank _ _).mpr (blanks 201 (by decide +kernel) (by decide) (by decide) (by decide))
  · exact (zero_word_iff_blank _ _).mpr (blanks 700 (by decide +kernel) (by decide) (by decide) (by decide))
  · intro i hi
    have subset : (PhaseMachine.Runtime.ids.erase 652).erase 653⊆freshTapes:=by decide +kernel
    have bounds : ∀i∈(PhaseMachine.Runtime.ids.erase 652).erase 653,i<1000 ∧i≠660 ∧i≠705:=by decide +kernel
    exact blanks i (subset hi) (bounds i hi).1 (bounds i hi).2.1 (bounds i hi).2.2
  · intro i hi
    have subset : GlueMachine.Runtime.ids.erase 640⊆freshTapes:=by decide +kernel
    have bounds : ∀i∈GlueMachine.Runtime.ids.erase 640,i<1000 ∧i≠660 ∧i≠705:=by decide +kernel
    exact blanks i (subset hi) (bounds i hi).1 (bounds i hi).2.1 (bounds i hi).2.2
  · refine ⟨blanks 4 (by decide +kernel) (by decide) (by decide) (by decide),?_⟩
    intro i hi
    have subset : DyadicFloor.extraIds∪NaturalQuotient.workPorts⊆freshTapes:=by decide +kernel
    have bounds : ∀i∈DyadicFloor.extraIds∪NaturalQuotient.workPorts,i<1000 ∧i≠660 ∧i≠705:=by decide +kernel
    exact blanks i (subset hi) (bounds i hi).1 (bounds i hi).2.1 (bounds i hi).2.2
  · refine ⟨ready.2 0 (by decide),ready.2 1 (by decide),ready.2 2 (by decide),ready.2 3 (by decide),?_,?_,?_,?_⟩
    all_goals exact blanks _ (by decide +kernel) (by decide) (by decide) (by decide)
  · exact blanks 7 (by decide +kernel) (by decide) (by decide) (by decide)
  · exact blanks 37 (by decide +kernel) (by decide) (by decide) (by decide)
  · exact blanks 205 (by decide +kernel) (by decide) (by decide) (by decide)
  · exact blanks 215 (by decide +kernel) (by decide) (by decide) (by decide)
  · exact blanks 216 (by decide +kernel) (by decide) (by decide) (by decide)
  · intro i hi
    have subset : serializerPorts⊆freshTapes:=by decide +kernel
    have bounds : ∀i∈serializerPorts,i<1000 ∧i≠660 ∧i≠705:=by decide +kernel
    exact blanks i (subset hi) (bounds i hi).1 (bounds i hi).2.1 (bounds i hi).2.2
  · exact (frame.tapes 991 (by decide +kernel)).trans (fresh 991 (by decide +kernel))

#print axioms freshStartup_executes
end Maxwell.Continuum.Profile.Runtime
