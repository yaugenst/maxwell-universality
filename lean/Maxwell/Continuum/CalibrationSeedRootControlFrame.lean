import Maxwell.Continuum.CalibrationSeedRootTestMachine
import Maxwell.Continuum.CalibrationSeedRootTerm

/-! The natural support test shares comparison scratch with rational
arithmetic. Its actual cleanup restores that bank before reading the cache. -/
namespace Maxwell.Continuum.Calibration.SeedRoot
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 3000000
set_option maxRecDepth 12000

def clearComparison : List NatAssign.Instruction :=
  [.literal 30 0,.literal 31 0,.literal 32 0,.literal 33 0,.literal 34 0,.literal 35 0,.literal 36 0]
def cleared (v : ℕ→ℕ) := NatAssign.values clearComparison v
def cleanupCost (B : ℕ) : ℕ := 3000*8^7*(B+2)^2

theorem clearComparison_valid : ∀a∈clearComparison,a.Valid ids := by
  simp [clearComparison,NatAssign.Instruction.Valid,ids,SelectedParameters.Compare.ids]
theorem cleared_zero (v : ℕ→ℕ) (i : ℕ) (hi : i∈RationalMagnitude.ids) : cleared v i=0 := by
  simp only [RationalMagnitude.ids,Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [cleared,clearComparison,NatAssign.values,NatAssign.Instruction.update,NatAssign.Instruction.target,
      NatAssign.Instruction.value]
theorem cleared_keep (v : ℕ→ℕ) (i : ℕ) (hi : i∉RationalMagnitude.ids) : cleared v i=v i := by
  apply NatAssign.values_preserves
  simp only [RationalMagnitude.ids,Finset.mem_insert,Finset.mem_singleton,not_or] at hi
  simp [clearComparison,NatAssign.Instruction.target,hi.1,hi.2.1,hi.2.2.1,hi.2.2.2.1,
    hi.2.2.2.2.1,hi.2.2.2.2.2.1,hi.2.2.2.2.2.2]

theorem cleanup_executes (v : ℕ→ℕ) (B : ℕ) (width : ∀i∈ids,(v i).bits.length≤B)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (bank : NatAssign.Bank ids v s.val) (scratch : NatAssign.Scratch s.val) :
    ∃cost t,Executes input tape (NatAssign.code clearComparison) cost s t ∧ cost≤cleanupCost B ∧
      NatAssign.Bank ids (cleared v) t.val ∧ NatAssign.Scratch t.val ∧
      (∀i∈ids,(cleared v i).bits.length≤B) ∧
      BinaryPrecision.Frame workspace s.val t.val := by
  obtain ⟨cost,t,ex,bound,bt,st,frame⟩ := NatAssign.executes ids ids_lower clearComparison
    clearComparison_valid v input tape s bank scratch
  have literals : ∀a∈clearComparison,a.literalWidth≤B := by
    simp [clearComparison,NatAssign.Instruction.literalWidth]
  have price := NatAssign.price_bound ids clearComparison clearComparison_valid v B width literals
  refine ⟨cost,t,ex,bound.trans price,bt,st,?_,frame.mono
    (NatAssign.changes_subset ids clearComparison clearComparison_valid)⟩
  exact NatAssign.values_assignment_width ids clearComparison clearComparison_valid v B width
    (by simp [clearComparison,NatAssign.Instruction.AssignmentBound])

theorem rational_ready_after_control {S : Finset ℕ} {v : ℕ→Parts} {s t : Store}
    (ready : Ready S v s) (frame : BinaryPrecision.Frame workspace s.val t.val)
    (scratch : NatAssign.Scratch t.val)
    (zero : ∀i∈RationalMagnitude.ids,RationalAccumulator.Word t.val i 0) : Ready S v t := by
  refine ⟨?_,scratch⟩
  intro i hi
  by_cases hm : i∈RationalMagnitude.ids
  · have small : i<1000 := by
      simp only [RationalMagnitude.ids,Finset.mem_insert,Finset.mem_singleton] at hm
      omega
    rw [dataValues_small v small]
    exact zero i hm
  have outside : i∉workspace := by
    rcases Finset.mem_union.mp hi with hp|hw
    · obtain ⟨r,_,hr⟩ := Finset.mem_biUnion.mp hp
      have lower : 1000 ≤ i := by
        simp only [cellPorts,Finset.mem_insert,Finset.mem_singleton] at hr
        rcases hr with rfl|rfl|rfl
        · exact positivePort_ge r
        · exact negativePort_ge r
        · exact denominatorPort_ge r
      simp only [workspace,ids,extra,SelectedParameters.Compare.ids,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc]
      omega
    · have ht : i∈temporaryPorts := (Finset.mem_union.mp hw).resolve_right hm
      simp only [temporaryPorts,Finset.mem_insert,Finset.mem_singleton] at ht
      simp only [workspace,ids,extra,SelectedParameters.Compare.ids,Finset.mem_union,
        Finset.mem_insert,Finset.mem_singleton,Finset.mem_Icc]
      omega
  exact RationalAccumulator.word_of_eq (frame.tapes i outside) (ready.1 i hi)

theorem table_ready_after_control {T : ℕ} {a : PartArray.Table T} {s t : Store}
    (table : a.Ready s) (frame : BinaryPrecision.Frame workspace s.val t.val)
    (scratch : NatAssign.Scratch t.val) : a.Ready t := by
  refine ⟨⟨scratch 0 (by decide),scratch 1 (by decide),scratch 2 (by decide),
    scratch 3 (by decide),?_,?_,?_,?_⟩,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact RationalAccumulator.blank_of_eq (frame.tapes 5 (by decide)) table.scratch.2.2.2.2.1
  · exact RationalAccumulator.blank_of_eq (frame.tapes 6 (by decide)) table.scratch.2.2.2.2.2.1
  · exact RationalAccumulator.blank_of_eq (frame.tapes 8 (by decide)) table.scratch.2.2.2.2.2.2.1
  · exact RationalAccumulator.blank_of_eq (frame.tapes 9 (by decide)) table.scratch.2.2.2.2.2.2.2
  · exact RationalAccumulator.blank_of_eq (frame.tapes 7 (by decide)) table.seven
  · exact BankArray.word_of_eq (frame.tapes 200 (by decide)) table.width
  · exact BankArray.word_of_eq (frame.tapes 202 (by decide)) table.basePositive
  · exact BankArray.word_of_eq (frame.tapes 203 (by decide)) table.baseNegative
  · exact BankArray.word_of_eq (frame.tapes 204 (by decide)) table.baseDenominator
  · exact BankArray.word_of_eq (frame.tapes 205 (by decide)) table.clock
  · simpa only [frame.memory] using table.positive
  · simpa only [frame.memory] using table.negative
  · simpa only [frame.memory] using table.denominator

#print axioms rational_ready_after_control
#print axioms cleanup_executes
end Maxwell.Continuum.Calibration.SeedRoot
