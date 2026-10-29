import Maxwell.Cost.RealSaddleBuffer.Append

namespace Maxwell.Cost.RealSaddleBuffer
open RealSparseOrder (Buffer)
open RealSimulation.Control
open RealSparse (execute execute_sound)
set_option maxRecDepth 20000

def pairLoad : Machine := ⟨[
  .loadIndex 9 5, .indexAdd 11 5 1, .loadIndex 10 11,
  .indexAdd 10 70 10, .load 0 6, .halt]⟩
def pairSwap : Machine := ⟨[.indexCopy 11 9, .indexCopy 9 10, .indexCopy 10 11, .halt]⟩
def pairFinish : Machine := ⟨[
  .indexAdd 5 5 2, .indexAdd 6 6 1, .indexSubtract 3 3 1, .halt]⟩

noncomputable def pairLoaded (s : Store) : Store :=
  let t := s.val.setIndex 9 (s.val.indices (s.val.indices 5))
  let t := t.setIndex 11 (s.val.indices 5 + 1)
  let t := t.setIndex 10 (s.val.indices (s.val.indices 5 + 1))
  let t := t.setIndex 10 (s.val.indices 70 + s.val.indices (s.val.indices 5 + 1))
  Store.ofState (t.setWord 0 (s.val.words (s.val.indices 6)))
def pairSwapped (s : Store) : Store :=
  Store.ofState (((s.val.setIndex 11 (s.val.indices 9)).setIndex 9 (s.val.indices 10)).setIndex 10 (s.val.indices 9))
def pairFinished (s : Store) : Store :=
  Store.ofState (((s.val.setIndex 5 (s.val.indices 5 + 2)).setIndex 6 (s.val.indices 6 + 1)).setIndex 3 (s.val.indices 3 - 1))

theorem pairLoad_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store)
    (h1 : s.val.indices 1 = 1) (hc : 100 ≤ s.val.indices 5) :
    Executes input tape (.call pairLoad) 6 s (pairLoaded s) := by
  apply Executes.call _ _ _ 5
  · apply execute_sound
    have hlow : ∀ i < 20, s.val.indices 5 + 1 ≠ i := by omega
    simp [execute, pairLoad, Machine.next, s.property, h1,
      RAMState.setIndex, RAMState.setWord, hlow]
  · simp [pairLoad, RAMState.setIndex, RAMState.setWord, s.property]

theorem pairSwap_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store) :
    Executes input tape (.call pairSwap) 4 s (pairSwapped s) := by
  apply Executes.call _ _ _ 3
  · apply execute_sound
    simp [execute, pairSwap, Machine.next, s.property, RAMState.setIndex]
  · simp [pairSwap, RAMState.setIndex, s.property]

theorem pairFinish_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store)
    (h1 : s.val.indices 1 = 1) (h2 : s.val.indices 2 = 2) :
    Executes input tape (.call pairFinish) 4 s (pairFinished s) := by
  apply Executes.call _ _ _ 3
  · apply execute_sound
    simp [execute, pairFinish, Machine.next, s.property, h1, h2, RAMState.setIndex]
  · simp [pairFinish, RAMState.setIndex, s.property]

def pairCode : Code := .seq (.call pairLoad) (.seq (.call appendProgram)
  (.seq (.call pairSwap) (.seq (.call appendProgram) (.call pairFinish))))
def pairLoop : Code := .loop 1 3 pairCode

structure PairReady (src dst : Buffer) (s : Store) (rows start n : ℕ) : Prop where
  one : s.val.indices 1 = 1
  two : s.val.indices 2 = 2
  remaining : s.val.indices 3 = n
  sourceRow : s.val.indices 5 = src.row start
  sourceValue : s.val.indices 6 = src.value start
  targetRow : s.val.indices 7 = dst.coordinates
  targetValue : s.val.indices 8 = dst.coefficients
  rowCount : s.val.indices 70 = rows

end Maxwell.Cost.RealSaddleBuffer
