import Maxwell.Continuum.RationalDataflowArrayTransfer
import Maxwell.Cost.Structured.WordCopyPlan

/-! Promote an output table by copying its five actual descriptor words.
The overwritten input words may describe arbitrary old data. -/
namespace Maxwell.Continuum.RationalDataflow.PartArray
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def inputHeaderIds : Finset ℕ := {200,202,203,204,205}
def promoteIds : Finset ℕ := {200,202,203,204,205,210,212,213,214,215}
def promotePlan : List (ℕ×ℕ) := [(210,200),(212,202),(213,203),(214,204),(215,205)]
def promoteCode : Code := WordCopyPlan.code promotePlan

def promoteValues {n : ℕ} (a : Table n) (old : ℕ→List Bool) (i : ℕ) : List Bool :=
  if i=210 then a.width else if i=212 then a.basePositive else if i=213 then a.baseNegative
    else if i=214 then a.baseDenominator else if i=215 then a.clock else old i

theorem Table.OutputReady.promote {n M : ℕ} (a : Table n) (hm : a.MetadataWidth M)
    (old : ℕ→List Bool) (width : ∀i∈inputHeaderIds,(old i).length ≤ M)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (h : a.OutputReady s)
    (words : ∀i∈inputHeaderIds,BankArray.Word s.val i (old i)) :
    ∃cost t,Executes input tape promoteCode cost s t ∧ cost ≤ 105*M+106 ∧
      a.Ready t ∧ BinaryPrecision.Frame inputHeaderIds s.val t.val := by
  have bank : WordCopyPlan.Bank promoteIds (promoteValues a old) s.val := by
    intro i hi
    simp only [promoteIds,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · simpa [promoteValues] using words 200 (by decide)
    · simpa [promoteValues] using words 202 (by decide)
    · simpa [promoteValues] using words 203 (by decide)
    · simpa [promoteValues] using words 204 (by decide)
    · simpa [promoteValues] using words 205 (by decide)
    · simpa [promoteValues] using h.width
    · simpa [promoteValues] using h.basePositive
    · simpa [promoteValues] using h.baseNegative
    · simpa [promoteValues] using h.baseDenominator
    · simpa [promoteValues] using h.clock
  have lengths : ∀i∈promoteIds,(promoteValues a old i).length ≤ M := by
    intro i hi
    simp only [promoteIds,Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · simpa [promoteValues] using width 200 (by decide)
    · simpa [promoteValues] using width 202 (by decide)
    · simpa [promoteValues] using width 203 (by decide)
    · simpa [promoteValues] using width 204 (by decide)
    · simpa [promoteValues] using width 205 (by decide)
    · simpa [promoteValues] using hm.width
    · simpa [promoteValues] using hm.basePositive
    · simpa [promoteValues] using hm.baseNegative
    · simpa [promoteValues] using hm.baseDenominator
    · simpa [promoteValues] using hm.clock
  obtain ⟨cost,t,ex,hc,bt,_,frame⟩ := WordCopyPlan.executes promoteIds M promotePlan (by decide)
    (promoteValues a old) lengths input tape s bank
  have ft : BinaryPrecision.Frame inputHeaderIds s.val t.val := by
    simpa only [promotePlan,WordCopyPlan.targets,List.map_cons,List.map_nil,List.toFinset_cons,
      List.toFinset_nil,Finset.insert_empty,inputHeaderIds] using frame
  have keep (k : ℕ) (hk : k<10) := ft.tapes k (by
    simp only [inputHeaderIds,Finset.mem_insert,Finset.mem_singleton];omega)
  have scratch : BankArray.Scratch t.val :=
    ⟨blank_of_eq (keep 0 (by decide)) h.scratch.1,blank_of_eq (keep 1 (by decide)) h.scratch.2.1,
      blank_of_eq (keep 2 (by decide)) h.scratch.2.2.1,blank_of_eq (keep 3 (by decide)) h.scratch.2.2.2.1,
      blank_of_eq (keep 5 (by decide)) h.scratch.2.2.2.2.1,blank_of_eq (keep 6 (by decide)) h.scratch.2.2.2.2.2.1,
      blank_of_eq (keep 8 (by decide)) h.scratch.2.2.2.2.2.2.1,blank_of_eq (keep 9 (by decide)) h.scratch.2.2.2.2.2.2.2⟩
  refine ⟨cost,t,ex,by simp only [promotePlan,List.length_cons,List.length_nil] at hc;omega,
    ⟨scratch,blank_of_eq (keep 7 (by decide)) h.seven,?_,?_,?_,?_,?_,?_,?_,?_⟩,ft⟩
  · simpa [promotePlan,WordCopyPlan.evaluate,promoteValues] using bt 200 (by decide)
  · simpa [promotePlan,WordCopyPlan.evaluate,promoteValues] using bt 202 (by decide)
  · simpa [promotePlan,WordCopyPlan.evaluate,promoteValues] using bt 203 (by decide)
  · simpa [promotePlan,WordCopyPlan.evaluate,promoteValues] using bt 204 (by decide)
  · simpa [promotePlan,WordCopyPlan.evaluate,promoteValues] using bt 205 (by decide)
  · simpa only [ft.memory] using h.positive
  · simpa only [ft.memory] using h.negative
  · simpa only [ft.memory] using h.denominator

#print axioms Table.OutputReady.promote
end Maxwell.Continuum.RationalDataflow.PartArray
