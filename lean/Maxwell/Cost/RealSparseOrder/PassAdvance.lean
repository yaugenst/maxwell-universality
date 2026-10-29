import Maxwell.Cost.RealSparseOrder.DataFrame

namespace Maxwell.Cost.RealSparseOrder.PassAdvance
open RealSparse (execute execute_sound)
open RealSimulation.Control

def program : Machine := ⟨[
  .indexSubtract 17 17 24,.indexAdd 19 19 25,.indexAdd 20 20 24,
  .indexAdd 21 21 25,.indexAdd 22 22 24,.halt]⟩

noncomputable def advanced (s : RAMState) : RAMState :=
  let t := s.setIndex 17 (s.indices 17-s.indices 24)
  let t := t.setIndex 19 (s.indices 19+s.indices 25)
  let t := t.setIndex 20 (s.indices 20+s.indices 24)
  let t := t.setIndex 21 (s.indices 21+s.indices 25)
  t.setIndex 22 (s.indices 22+s.indices 24)

theorem steps (input : RAMInput) (tape : ℕ→Bool) (s : RAMState) (hp : s.pc=0) :
    execute (program.next input tape) 5 s=some (advanced s) := by
  simp [execute,program,Machine.next,RAMState.setIndex,advanced,hp]

theorem executes (input : RAMInput) (tape : ℕ→Bool) (s : Store) :
    Executes input tape (.call program) 6 s (Store.ofState (advanced s.val)) := by
  apply Executes.call _ s _ 5 (execute_sound _ (steps input tape s.val s.property))
  simp [program,advanced,RAMState.setIndex,s.property]

theorem indices_frame (s : RAMState) (j : ℕ) (hj : j<17 ∨26≤j) :
    (advanced s).indices j=s.indices j := by
  simp [advanced,RAMState.setIndex,show j≠17 by omega,show j≠19 by omega,
    show j≠20 by omega,show j≠21 by omega,show j≠22 by omega]

theorem data_frame (s : RAMState) (out : Buffer) : DataFrame out 0 s (advanced s) := by
  constructor
  · intro j hj _
    exact indices_frame s j (Or.inr (by omega))
  · intro _ _ _; rfl

end Maxwell.Cost.RealSparseOrder.PassAdvance
