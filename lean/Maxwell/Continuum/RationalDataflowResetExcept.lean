import Maxwell.Continuum.RationalDataflowRetainedReset
import Maxwell.Continuum.RationalDataflowBankPartition

/-! Reset a represented arithmetic bank while retaining a declared subbank.
The result width depends on the retained values, while the old width is used
only to charge the actual clearing work. -/
namespace Maxwell.Continuum.RationalDataflow.ResetExcept
open Maxwell.Cost Maxwell.Cost.Structured

def values (T : Finset ℕ) (v : ℕ→Parts) (i : ℕ) : Parts :=
  if i∈T then v i else Initialize.parts i

theorem executes (S T : Finset ℕ) (v : ℕ→Parts) (B C : ℕ) (positive : 1≤B)
    (oldWidth : WidthBank S B v) (retainedWidth : WidthBank T C v) (retainedGood : Good T v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (ready : Ready S v s) :
    ∃steps t,Executes input tape (Initialize.code (S\T)) steps s t ∧
      steps≤Initialize.resetCost (S\T) B ∧ Ready S (values T v) t ∧
      Good S (values T v) ∧ WidthBank S (max 1 C) (values T v) ∧
      BinaryPrecision.Frame (workspace (S\T)) s.val t.val := by
  have clearedWidth : WidthBank (S\T) B v := fun i hi=>oldWidth i (Finset.mem_sdiff.mp hi).1
  obtain ⟨steps,t,execution,charge,clear,frame⟩:=Initialize.reset_executes (S\T) v B positive
    clearedWidth input tape s (ready.restrict Finset.sdiff_subset)
  have oldCells : Cells (S∩T) v s.val := fun i hi=>Cells.of_ready ready i (Finset.mem_inter.mp hi).1
  have retainedCells : Cells (S∩T) v t.val := oldCells.frame frame (by
    apply Finset.disjoint_left.mpr
    intro i kept erased
    exact (Finset.mem_sdiff.mp erased).2 (Finset.mem_inter.mp kept).2)
  have cells : Cells S (values T v) t.val := by
    intro i hi
    by_cases retained : i∈T
    · simpa only [values,ite_eq_left retained] using retainedCells i (Finset.mem_inter.mpr ⟨hi,retained⟩)
    · simpa only [values,ite_eq_right retained] using Cells.of_ready clear i (Finset.mem_sdiff.mpr ⟨hi,retained⟩)
  refine ⟨steps,t,execution,charge,cells.ready_with clear,?_,?_,frame⟩
  · intro i hi
    by_cases retained : i∈T
    · simpa only [values,ite_eq_left retained] using retainedGood i retained
    · simpa only [values,ite_eq_right retained] using Initialize.good S i hi
  · intro i hi
    by_cases retained : i∈T
    · simpa only [values,ite_eq_left retained] using (retainedWidth i retained).mono (le_max_right _ _)
    · simpa only [values,ite_eq_right retained] using (Initialize.width S i hi).mono (le_max_left _ _)

#print axioms executes
end Maxwell.Continuum.RationalDataflow.ResetExcept
