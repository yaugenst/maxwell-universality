import Maxwell.Cost.RealSparseOrder.SortState
import Maxwell.Cost.RealSparseOrder.Load

namespace Maxwell.Cost.RealSparseOrder.Initialize
open RealSparse (execute execute_sound input)
open RealSimulation.Control

def secondaryBuffer (m : ℕ) : Buffer := ⟨100+m,100+2*m⟩

def program : Machine := ⟨[
  .indexLiteral 0 0,.indexLiteral 1 1,.indexLiteral 2 2,
  .indexLiteral 18 1,.inputIndex 26 0,.indexLiteral 27 100,.indexLiteral 28 100,
  .indexAdd 29 26 26,.indexAdd 29 29 27,.indexAdd 30 26 28,.halt]⟩

noncomputable def initialized (m : ℕ) (s : RAMState) : RAMState :=
  let t := s.setIndex 0 0
  let t := t.setIndex 1 1
  let t := t.setIndex 2 2
  let t := t.setIndex 18 1
  let t := t.setIndex 26 m
  let t := t.setIndex 27 100
  let t := t.setIndex 28 100
  let t := t.setIndex 29 (m+m)
  let t := t.setIndex 29 (m+m+100)
  t.setIndex 30 (m+100)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 500000 in
theorem steps (es : List SparseEntry) (vector : ℕ→ℝ) (tape : ℕ→Bool)
    (s : RAMState) (hp : s.pc=0) :
    execute (program.next (input es vector) tape) 10 s=some (initialized es.length s) := by
  simp [execute,program,Machine.next,RAMState.setIndex,initialized,hp]

theorem executes (es : List SparseEntry) (vector : ℕ→ℝ) (tape : ℕ→Bool) (s : Store) :
    Executes (input es vector) tape (.call program) 11 s
      (Store.ofState (initialized es.length s.val)) := by
  apply Executes.call _ s _ 10 (execute_sound _ (steps es vector tape s.val s.property))
  simp [program,initialized,RAMState.setIndex,s.property]

theorem indices_frame (m : ℕ) (s : RAMState) (j : ℕ) (hj : 31≤j) :
    (initialized m s).indices j=s.indices j := by
  simp [initialized,RAMState.setIndex,show j≠0 by omega,show j≠1 by omega,
    show j≠2 by omega,show j≠18 by omega,show j≠26 by omega,show j≠27 by omega,
    show j≠28 by omega,show j≠29 by omega,show j≠30 by omega]

theorem data_frame (m : ℕ) (s : RAMState) (out : Buffer) : DataFrame out 0 s (initialized m s) := by
  constructor
  · intro j hj _; exact indices_frame m s j (by omega)
  · intro _ _ _; rfl

theorem invariant (es : List SparseEntry) (s : RAMState) (h : Stored initialBuffer s es) :
    Sort.Invariant (initialized es.length s) initialBuffer (secondaryBuffer es.length) 1
      (singletonRuns es) := by
  refine ⟨?_,by simp [Buffer.Safe,initialBuffer],by simp [Buffer.Safe,secondaryBuffer],?_,?_⟩
  · constructor <;> simp [initialized,RAMState.setIndex,initialBuffer,secondaryBuffer,
      two_mul,Nat.add_comm]
  · rw [singletonRuns_flatten]
    exact ((records_stored _ _ _).mpr h).dataFrame_zero (by simp [Buffer.Safe,initialBuffer])
      (data_frame es.length s initialBuffer)
  · simp [Separated,initialBuffer,secondaryBuffer]

end Maxwell.Cost.RealSparseOrder.Initialize
