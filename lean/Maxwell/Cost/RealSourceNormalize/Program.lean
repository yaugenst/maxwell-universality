import Maxwell.Cost.RealSourceSerialize.Primitives
import Maxwell.Cost.RealArrayNormalize.Correctness

namespace Maxwell.Cost.RealSourceNormalize
open RealSimulation.Control
open RealSparse (execute execute_sound)
set_option maxRecDepth 20000

def prepareMatrix : Machine := ⟨[.indexCopy 55 25, .indexCopy 26 53, .halt]⟩
def prepareSource : Machine := ⟨[.indexCopy 25 54, .indexCopy 26 52, .halt]⟩
def saveScale (dst : ℕ) : Machine := ⟨[.copy dst 7, .halt]⟩

def matrixState (s : Store) : Store :=
  Store.ofState ((s.val.setIndex 55 (s.val.indices 25)).setIndex 26 (s.val.indices 53))
def sourceState (s : Store) : Store :=
  Store.ofState ((s.val.setIndex 25 (s.val.indices 54)).setIndex 26 (s.val.indices 52))
noncomputable def savedState (dst : ℕ) (s : Store) : Store :=
  Store.ofState (s.val.setWord dst (s.val.words 7))

theorem matrix_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store) :
    Executes input tape (.call prepareMatrix) 3 s (matrixState s) := by
  apply Executes.call _ _ _ 2
  · apply execute_sound
    simp [execute, prepareMatrix, Machine.next, s.property, RAMState.setIndex]
  · simp [prepareMatrix, RAMState.setIndex, s.property]

theorem source_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store) :
    Executes input tape (.call prepareSource) 3 s (sourceState s) := by
  apply Executes.call _ _ _ 2
  · apply execute_sound
    simp [execute, prepareSource, Machine.next, s.property, RAMState.setIndex]
  · simp [prepareSource, RAMState.setIndex, s.property]

theorem save_executes (input : RAMInput) (tape : ℕ → Bool) (dst : ℕ) (s : Store) :
    Executes input tape (.call (saveScale dst)) 2 s (savedState dst s) := by
  apply Executes.call _ _ _ 1
  · apply execute_sound
    simp [execute, saveScale, Machine.next, s.property]
  · simp [saveScale, RAMState.setWord, s.property]

def code : Code := .seq (.call prepareMatrix)
  (.seq (.call (RealArrayNormalize.program true)) (.seq (.call (saveScale 20))
    (.seq (.call prepareSource) (.seq (.call (RealArrayNormalize.program false))
      (.seq (.call (saveScale 21)) (.call (RealSourceSerialize.copyProgram 25 55)))))))

def program : Machine := code.compile

end Maxwell.Cost.RealSourceNormalize
