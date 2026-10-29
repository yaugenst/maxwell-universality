import Maxwell.Cost.RealSaddleBuffer.Diagonal
import Maxwell.Cost.RealSaddleBuffer.PairLoop

namespace Maxwell.Cost.RealSaddleBuffer
open RealSimulation.Control
open RealSparse (execute execute_sound)
set_option maxRecDepth 20000

/-- Caller metadata70..77 holds rows, columns, padding, input count,
source coordinate/value bases, and destination coordinate/value bases. -/
def initializeProgram : Machine := ⟨[
  .indexLiteral 0 0, .indexLiteral 1 1, .indexLiteral 2 2,
  .indexCopy 3 70, .indexLiteral 4 0, .indexCopy 7 76, .indexCopy 8 77, .halt]⟩
def preparePairs : Machine := ⟨[.indexCopy 3 73, .indexCopy 5 74, .indexCopy 6 75, .halt]⟩
def preparePadding : Machine := ⟨[.indexCopy 3 72, .indexAdd 4 70 71, .halt]⟩

def initialized (s : Store) : Store :=
  let t := s.val.setIndex 0 0
  let t := t.setIndex 1 1
  let t := t.setIndex 2 2
  let t := t.setIndex 3 (s.val.indices 70)
  let t := t.setIndex 4 0
  let t := t.setIndex 7 (s.val.indices 76)
  Store.ofState (t.setIndex 8 (s.val.indices 77))
def pairsPrepared (s : Store) : Store :=
  Store.ofState (((s.val.setIndex 3 (s.val.indices 73)).setIndex 5 (s.val.indices 74)).setIndex 6 (s.val.indices 75))
def paddingPrepared (s : Store) : Store :=
  Store.ofState ((s.val.setIndex 3 (s.val.indices 72)).setIndex 4 (s.val.indices 70 + s.val.indices 71))

theorem initialize_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store) :
    Executes input tape (.call initializeProgram) 8 s (initialized s) := by
  apply Executes.call _ _ _ 7
  · apply execute_sound
    simp [execute, initializeProgram, Machine.next, s.property, RAMState.setIndex]
  · simp [initializeProgram, RAMState.setIndex, s.property]

theorem preparePairs_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store) :
    Executes input tape (.call preparePairs) 4 s (pairsPrepared s) := by
  apply Executes.call _ _ _ 3
  · apply execute_sound
    simp [execute, preparePairs, Machine.next, s.property, RAMState.setIndex]
  · simp [preparePairs, RAMState.setIndex, s.property]

theorem preparePadding_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store) :
    Executes input tape (.call preparePadding) 3 s (paddingPrepared s) := by
  apply Executes.call _ _ _ 2
  · apply execute_sound
    simp [execute, preparePadding, Machine.next, s.property, RAMState.setIndex]
  · simp [preparePadding, RAMState.setIndex, s.property]

theorem initialized_scratch (s : Store) : Scratch s.val (initialized s).val := by
  refine ⟨fun _ _ => rfl, ?_, rfl, rfl, rfl⟩
  intro i hi
  have hsmall : ∀ j < 9, i ≠ j := by omega
  simp [initialized, Store.ofState, RAMState.setIndex, hsmall]

theorem pairsPrepared_scratch (s : Store) : Scratch s.val (pairsPrepared s).val := by
  refine ⟨fun _ _ => rfl, ?_, rfl, rfl, rfl⟩
  intro i hi
  simp [pairsPrepared, Store.ofState, RAMState.setIndex,
    show i ≠ 3 by omega, show i ≠ 5 by omega, show i ≠ 6 by omega]

theorem paddingPrepared_scratch (s : Store) : Scratch s.val (paddingPrepared s).val := by
  refine ⟨fun _ _ => rfl, ?_, rfl, rfl, rfl⟩
  intro i hi
  simp [paddingPrepared, Store.ofState, RAMState.setIndex, show i ≠ 3 by omega, show i ≠ 4 by omega]

def code : Code := .seq (.call initializeProgram) (.seq diagonalLoop
  (.seq (.call preparePairs) (.seq pairLoop (.seq (.call preparePadding) diagonalLoop))))
def program : Machine := code.compile

end Maxwell.Cost.RealSaddleBuffer
