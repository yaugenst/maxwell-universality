import Maxwell.Cost.RealSparseOrder.PassSetup

namespace Maxwell.Cost.RealSparseOrder.OuterControl
open RealSparse (execute execute_sound)
open RealSimulation.Control

/-- Copy the outer descriptors into the current pass's cursor bank. -/
def prepareProgram : Machine := ⟨[
  .indexCopy 17 26,.indexCopy 19 27,.indexCopy 20 28,
  .indexCopy 21 29,.indexCopy 22 30,.halt]⟩

noncomputable def prepared (s : RAMState) : RAMState :=
  let t := s.setIndex 17 (s.indices 26)
  let t := t.setIndex 19 (s.indices 27)
  let t := t.setIndex 20 (s.indices 28)
  let t := t.setIndex 21 (s.indices 29)
  t.setIndex 22 (s.indices 30)

theorem prepare_steps (input : RAMInput) (tape : ℕ→Bool) (s : RAMState) (hp : s.pc=0) :
    execute (prepareProgram.next input tape) 5 s=some (prepared s) := by
  simp [execute,prepareProgram,Machine.next,RAMState.setIndex,prepared,hp]

theorem prepare_executes (input : RAMInput) (tape : ℕ→Bool) (s : Store) :
    Executes input tape (.call prepareProgram) 6 s (Store.ofState (prepared s.val)) := by
  apply Executes.call _ s _ 5 (execute_sound _ (prepare_steps input tape s.val s.property))
  simp [prepareProgram,prepared,RAMState.setIndex,s.property]

theorem prepare_registers (s : RAMState) :
    (prepared s).indices 17=s.indices 26 ∧
    (prepared s).indices 19=s.indices 27 ∧
    (prepared s).indices 20=s.indices 28 ∧
    (prepared s).indices 21=s.indices 29 ∧
    (prepared s).indices 22=s.indices 30 := by
  simp [prepared,RAMState.setIndex]

theorem prepare_indices_frame (s : RAMState) (j : ℕ) (hj : j<17 ∨j=18 ∨23≤j) :
    (prepared s).indices j=s.indices j := by
  simp [prepared,RAMState.setIndex,show j≠17 by omega,show j≠19 by omega,
    show j≠20 by omega,show j≠21 by omega,show j≠22 by omega]

theorem prepare_words_frame (s : RAMState) : (prepared s).words=s.words := rfl

theorem prepare_data_frame (s : RAMState) (out : Buffer) : DataFrame out 0 s (prepared s) := by
  constructor
  · intro j hj _
    exact prepare_indices_frame s j (Or.inr (Or.inr (by omega)))
  · intro _ _ _; rfl

/-- Swap the two data buffers through one temporary register and double
the run width. The count in register twenty-six remains fixed. -/
def advanceProgram : Machine := ⟨[
  .indexCopy 31 27,.indexCopy 27 29,.indexCopy 29 31,
  .indexCopy 31 28,.indexCopy 28 30,.indexCopy 30 31,
  .indexAdd 18 18 18,.halt]⟩

noncomputable def advanced (s : RAMState) : RAMState :=
  let t := s.setIndex 31 (s.indices 27)
  let t := t.setIndex 27 (s.indices 29)
  let t := t.setIndex 29 (s.indices 27)
  let t := t.setIndex 31 (s.indices 28)
  let t := t.setIndex 28 (s.indices 30)
  let t := t.setIndex 30 (s.indices 28)
  t.setIndex 18 (s.indices 18+s.indices 18)

theorem advance_steps (input : RAMInput) (tape : ℕ→Bool) (s : RAMState) (hp : s.pc=0) :
    execute (advanceProgram.next input tape) 7 s=some (advanced s) := by
  simp [execute,advanceProgram,Machine.next,RAMState.setIndex,advanced,hp]

theorem advance_executes (input : RAMInput) (tape : ℕ→Bool) (s : Store) :
    Executes input tape (.call advanceProgram) 8 s (Store.ofState (advanced s.val)) := by
  apply Executes.call _ s _ 7 (execute_sound _ (advance_steps input tape s.val s.property))
  simp [advanceProgram,advanced,RAMState.setIndex,s.property]

theorem advance_registers (s : RAMState) :
    (advanced s).indices 18=2*s.indices 18 ∧
    (advanced s).indices 27=s.indices 29 ∧
    (advanced s).indices 28=s.indices 30 ∧
    (advanced s).indices 29=s.indices 27 ∧
    (advanced s).indices 30=s.indices 28 ∧
    (advanced s).indices 31=s.indices 28 := by
  simp [advanced,RAMState.setIndex,two_mul]

theorem advance_indices_frame (s : RAMState) (j : ℕ)
    (hj : j<18 ∨(19≤j ∧j<27) ∨32≤j) : (advanced s).indices j=s.indices j := by
  simp [advanced,RAMState.setIndex,show j≠18 by omega,show j≠27 by omega,
    show j≠28 by omega,show j≠29 by omega,show j≠30 by omega,show j≠31 by omega]

theorem advance_words_frame (s : RAMState) : (advanced s).words=s.words := rfl

theorem advance_data_frame (s : RAMState) (out : Buffer) : DataFrame out 0 s (advanced s) := by
  constructor
  · intro j hj _
    exact advance_indices_frame s j (Or.inr (Or.inr (by omega)))
  · intro _ _ _; rfl

end Maxwell.Cost.RealSparseOrder.OuterControl
