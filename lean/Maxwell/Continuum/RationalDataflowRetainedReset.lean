import Maxwell.Continuum.RationalDataflowRetainedCells
import Maxwell.Continuum.RationalDataflowInitialize

/-! A represented raw bank can be reset after another arithmetic bank has
returned the common scratch. Old values need not be valid rationals. -/
namespace Maxwell.Continuum.RationalDataflow
open Maxwell.Cost Maxwell.Cost.Structured

theorem Cells.frame {S T : Finset ℕ} {v : ℕ→Parts} {s t : BitRAMState}
    (cells : Cells S v s) (frame : BinaryPrecision.Frame (workspace T) s t)
    (separate : Disjoint S T) : Cells S v t := by
  apply cells.transfer_tapes
  intro k hk
  obtain ⟨i,hi,cell⟩:=Finset.mem_biUnion.mp hk
  have low : 1000 ≤ k := by
    simp only [cellPorts,positivePort,negativePort,denominatorPort,
      Finset.mem_insert,Finset.mem_singleton] at cell
    omega
  apply frame.tapes
  intro changed
  rcases Finset.mem_union.mp changed with scratch | bank
  · simp only [Finset.mem_insert,Finset.mem_singleton] at scratch
    omega
  rcases Finset.mem_union.mp bank with raw | work
  · obtain ⟨j,hj,other⟩:=Finset.mem_biUnion.mp raw
    have equal : i=j := by
      simp only [cellPorts,positivePort,negativePort,denominatorPort,
        Finset.mem_insert,Finset.mem_singleton] at cell other
      omega
    exact Finset.disjoint_left.mp separate hi (equal ▸ hj)
  · simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton] at work
    omega

theorem Cells.ready_with {S T : Finset ℕ} {v w : ℕ→Parts} {s : Store}
    (cells : Cells S v s.val) (ready : Ready T w s) : Ready S v s := by
  apply cells.ready ?_ ready.2
  intro k hk
  have low : k < 1000 := by
    simp only [workPorts,temporaryPorts,RationalMagnitude.ids,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton] at hk
    omega
  have word:=ready.1 k (Finset.mem_union_right _ hk)
  simpa only [dataValues_small w low,RationalAccumulator.zero_word_iff_blank] using word

theorem Cells.reset_executes (S T : Finset ℕ) (v w : ℕ→Parts) (B : ℕ)
    (positive : 1 ≤ B) (width : WidthBank S B v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (cells : Cells S v s.val) (ready : Ready T w s) :
    ∃steps t,Executes input tape (Initialize.code S) steps s t ∧
      steps ≤ Initialize.resetCost S B ∧ Ready S Initialize.parts t ∧
      BinaryPrecision.Frame (workspace S) s.val t.val :=
  Initialize.reset_executes S v B positive width input tape s (cells.ready_with ready)

theorem Cells.reset_disjoint_executes (S T : Finset ℕ) (v w : ℕ→Parts) (B : ℕ)
    (separate : Disjoint S T) (positive : 1 ≤ B) (width : WidthBank S B v)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (cells : Cells S v s.val) (ready : Ready T w s) :
    ∃steps t,Executes input tape (Initialize.code S) steps s t ∧
      steps ≤ Initialize.resetCost S B ∧ Ready S Initialize.parts t ∧ Ready T w t ∧
      BinaryPrecision.Frame (workspace S) s.val t.val := by
  obtain ⟨steps,t,execution,charge,clear,frame⟩:=
    cells.reset_executes S T v w B positive width input tape s ready
  exact ⟨steps,t,execution,charge,clear,
    ((Cells.of_ready ready).frame frame separate.symm).ready_with clear,frame⟩

#print axioms Cells.reset_executes
#print axioms Cells.reset_disjoint_executes
end Maxwell.Continuum.RationalDataflow
