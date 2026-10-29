import Maxwell.Cost.RealArrayZero.Correctness

namespace Maxwell.Cost.RealSaddleSource
open RealSparse (execute execute_sound)
open RealSimulation.Control
set_option maxRecDepth 20000

/-- Metadata70/71/72 is the terminal row count, column count, and padding;
80 is the preserved transpose-product base, and54 is the source-vector base. -/
def prepareZero : Machine := ⟨[
  .indexCopy 56 54, .indexAdd 57 70 71, .indexAdd 57 57 72, .halt]⟩
def prepareCopy : Machine := ⟨[
  .indexCopy 55 80, .indexAdd 56 54 70, .indexCopy 57 71, .halt]⟩

def zeroPrepared (s : Store) : Store :=
  let t := s.val.setIndex 56 (s.val.indices 54)
  let t := t.setIndex 57 (s.val.indices 70 + s.val.indices 71)
  Store.ofState (t.setIndex 57 (s.val.indices 70 + s.val.indices 71 + s.val.indices 72))
def copyPrepared (s : Store) : Store :=
  let t := s.val.setIndex 55 (s.val.indices 80)
  let t := t.setIndex 56 (s.val.indices 54 + s.val.indices 70)
  Store.ofState (t.setIndex 57 (s.val.indices 71))

theorem prepareZero_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store) :
    Executes input tape (.call prepareZero) 4 s (zeroPrepared s) := by
  apply Executes.call _ _ _ 3
  · apply execute_sound
    simp [execute, prepareZero, Machine.next, s.property, RAMState.setIndex]
  · simp [prepareZero, RAMState.setIndex, s.property]

theorem prepareCopy_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store) :
    Executes input tape (.call prepareCopy) 4 s (copyPrepared s) := by
  apply Executes.call _ _ _ 3
  · apply execute_sound
    simp [execute, prepareCopy, Machine.next, s.property, RAMState.setIndex]
  · simp [prepareCopy, RAMState.setIndex, s.property]

def code : Code := .seq (.call prepareZero) (.seq (.call RealArrayZero.program)
  (.seq (.call prepareCopy) (.call (RealArrayCopy.program true))))
def program : Machine := code.compile

def rhs (rows columns : ℕ) (q : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j < rows then 0 else if j < rows + columns then -q (j - rows) else 0

structure Frame (dst n : ℕ) (s t : RAMState) : Prop where
  words : ∀ i, 2 ≤ i → (i < dst ∨ dst + n ≤ i) → t.words i = s.words i
  indices : ∀ i, 4 ≤ i → i ≠ 55 → i ≠ 56 → i ≠ 57 → t.indices i = s.indices i
  output : t.output = s.output
  indexOutput : t.indexOutput = s.indexOutput
  randomCursor : t.randomCursor = s.randomCursor

end Maxwell.Cost.RealSaddleSource
