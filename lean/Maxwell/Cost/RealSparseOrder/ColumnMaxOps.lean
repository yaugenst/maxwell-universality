import Maxwell.Cost.RealSparseOrder.ColumnMaxPure
import Maxwell.Cost.RealSparseOrder.Memory
import Maxwell.Cost.RealSimulation.ControlBounds

namespace Maxwell.Cost.RealSparseOrder.ColumnMax
open RealSparse (execute execute_sound)
open RealSimulation.Control RealSimulation.IndexWidth

def loadProgram : Machine := ⟨[.loadIndex 45 44,.indexAdd 45 45 1,.halt]⟩

noncomputable def loaded (s : RAMState) : RAMState :=
  let t := s.setIndex 45 (s.indices (s.indices 44))
  t.setIndex 45 (s.indices (s.indices 44)+1)

theorem load_executes (input : RAMInput) (tape : ℕ→Bool) (s : Store) (h1 : s.val.indices 1=1) :
    Executes input tape (.call loadProgram) 3 s (Store.ofState (loaded s.val)) := by
  apply Executes.call _ s _ 2
  · apply execute_sound
    simp [execute,loadProgram,Machine.next,loaded,RAMState.setIndex,s.property,h1]
  · simp [loadProgram,loaded,RAMState.setIndex,s.property]

def copyProgram : Machine := ⟨[.indexCopy 42 45,.halt]⟩
def chooseCode : Code := .branch 42 45 (.call copyProgram) .skip

noncomputable def chosen (s : Store) : Store :=
  if s.val.indices 42≤s.val.indices 45 then Store.ofState (s.val.setIndex 42 (s.val.indices 45)) else s

theorem choose_executes (input : RAMInput) (tape : ℕ→Bool) (s : Store) :
    ∃cost,cost≤3 ∧Executes input tape chooseCode cost s (chosen s) := by
  by_cases he : s.val.indices 42≤s.val.indices 45
  · refine ⟨3,by omega,?_⟩
    rw [chosen,ite_eq_left he]
    change Executes input tape (.branch 42 45 (.call copyProgram) .skip) 3 s _
    apply Executes.yes (cost:=2) he
    apply Executes.call _ s _ 1
    · apply execute_sound
      simp [execute,copyProgram,Machine.next,s.property]
    · simp [copyProgram,RAMState.setIndex,s.property]
  · refine ⟨2,by omega,?_⟩
    rw [chosen,ite_eq_right he]
    exact Executes.no he (Executes.skip s)

theorem chosen_max (s : Store) : (chosen s).val.indices 42=max (s.val.indices 42) (s.val.indices 45) := by
  by_cases he : s.val.indices 42≤s.val.indices 45
  · simp [chosen,he,Store.ofState,RAMState.setIndex]
  · simp [chosen,he,max_eq_left (le_of_not_ge he)]

theorem chosen_frame (s : Store) (j : ℕ) (hj : j≠42) : (chosen s).val.indices j=s.val.indices j := by
  by_cases he : s.val.indices 42≤s.val.indices 45 <;>
    simp [chosen,he,Store.ofState,RAMState.setIndex,hj]

theorem chosen_words (s : Store) : (chosen s).val.words=s.val.words := by
  by_cases he : s.val.indices 42≤s.val.indices 45 <;>
    simp [chosen,he,Store.ofState,RAMState.setIndex]

def advanceProgram : Machine := ⟨[.indexAdd 44 44 2,.indexSubtract 43 43 1,.halt]⟩

noncomputable def advanced (s : RAMState) : RAMState :=
  (s.setIndex 44 (s.indices 44+2)).setIndex 43 (s.indices 43-1)

theorem advance_executes (input : RAMInput) (tape : ℕ→Bool) (s : Store)
    (h1 : s.val.indices 1=1) (h2 : s.val.indices 2=2) :
    Executes input tape (.call advanceProgram) 3 s (Store.ofState (advanced s.val)) := by
  apply Executes.call _ s _ 2
  · apply execute_sound
    simp [execute,advanceProgram,Machine.next,advanced,RAMState.setIndex,s.property,h1,h2]
  · simp [advanceProgram,advanced,RAMState.setIndex,s.property]

def body : Code := .seq (.call loadProgram) (.seq chooseCode (.call advanceProgram))
def loopCode : Code := .loop 1 43 body

noncomputable def processed (s : Store) : Store :=
  Store.ofState (advanced (chosen (Store.ofState (loaded s.val))).val)

theorem step (input : RAMInput) (tape : ℕ→Bool) (s : Store)
    (h1 : s.val.indices 1=1) (h2 : s.val.indices 2=2) :
    ∃cost,cost≤9 ∧Executes input tape body cost s (processed s) := by
  let mid := Store.ofState (loaded s.val)
  obtain ⟨cost,hcost,run⟩ := choose_executes input tape mid
  have hm1 : (chosen mid).val.indices 1=1 := by
    rw [chosen_frame mid 1 (by decide)]
    simpa [mid,loaded,Store.ofState,RAMState.setIndex] using h1
  have hm2 : (chosen mid).val.indices 2=2 := by
    rw [chosen_frame mid 2 (by decide)]
    simpa [mid,loaded,Store.ofState,RAMState.setIndex] using h2
  exact ⟨3+(cost+3),by omega,Executes.seq (load_executes input tape s h1)
    (Executes.seq run (advance_executes input tape _ hm1 hm2))⟩

theorem processed_frame (s : Store) (j : ℕ) (hj : j<42 ∨46≤j) :
    (processed s).val.indices j=s.val.indices j := by
  simp only [processed,Store.ofState,advanced,RAMState.setIndex]
  rw [Function.update_of_ne (show j≠43 by omega),Function.update_of_ne (show j≠44 by omega),
    chosen_frame _ j (by omega)]
  simp [loaded,RAMState.setIndex,show j≠45 by omega]

theorem processed_words (s : Store) : (processed s).val.words=s.val.words := by
  change (chosen (Store.ofState (loaded s.val))).val.words=s.val.words
  exact chosen_words _

theorem processed_channels (s : Store) :
    (processed s).val.randomCursor=s.val.randomCursor ∧
    (processed s).val.output=s.val.output ∧(processed s).val.indexOutput=s.val.indexOutput := by
  unfold processed chosen
  split <;> simp [advanced,loaded,Store.ofState,RAMState.setIndex]

theorem processed_index_bound {B : ℕ} {s : Store} (hs : IndexBound B s.val)
    (hcol : s.val.indices (s.val.indices 44)+1≤B) (hcursor : s.val.indices 44+2≤B) :
    IndexBound B (processed s).val := by
  have hl : IndexBound B (loaded s.val) :=
    (hs.setIndex 45 _ (hs _)).setIndex 45 _ hcol
  have hc : IndexBound B (chosen (Store.ofState (loaded s.val))).val := by
    unfold chosen
    split
    · exact hl.setIndex 42 _ (hl 45)
    · exact hl
  apply (hc.setIndex 44 _ ?_).setIndex 43 _ ((Nat.sub_le _ _).trans (hc 43))
  rw [chosen_frame _ 44 (by decide)]
  simpa [loaded,Store.ofState,RAMState.setIndex] using hcursor

end Maxwell.Cost.RealSparseOrder.ColumnMax
