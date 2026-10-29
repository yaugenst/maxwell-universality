import Maxwell.Cost.RealArrayCopy.Correctness

namespace Maxwell.Cost.RealTransposePreserve
open RealSimulation.Control
open RealSparse (execute execute_sound)
set_option maxRecDepth 20000

/-- Preserve the actual transpose product before the sparse loader reuses
its low addressed array. The offset is computed by charged additions. -/
def prepare : Machine := ⟨[
  .indexLiteral 58 0, .inputIndex 57 58, .indexLiteral 55 16,
  .indexAdd 58 57 57, .indexAdd 59 58 58, .indexAdd 56 58 59,
  .indexLiteral 58 100, .indexAdd 56 56 58, .halt]⟩

def prepared (m : ℕ) (s : Store) : Store :=
  let t := s.val.setIndex 58 0
  let t := t.setIndex 57 m
  let t := t.setIndex 55 16
  let t := t.setIndex 58 (m + m)
  let t := t.setIndex 59 ((m + m) + (m + m))
  let t := t.setIndex 56 ((m + m) + ((m + m) + (m + m)))
  let t := t.setIndex 58 100
  Store.ofState (t.setIndex 56 ((m + m) + ((m + m) + (m + m)) + 100))

theorem prepare_executes (es : List SparseEntry) (vector : ℕ → ℝ)
    (tape : ℕ → Bool) (s : Store) :
    Executes (RealSparse.input es vector) tape (.call prepare) 9 s (prepared es.length s) := by
  apply Executes.call _ _ _ 8
  · apply execute_sound
    simp [execute, prepare, Machine.next, s.property, RAMState.setIndex]
  · simp [prepare, RAMState.setIndex, s.property]

def code : Code := .seq (.call RealSparse.program)
  (.seq (.call prepare) (.call (RealArrayCopy.program false)))
def program : Machine := code.compile

end Maxwell.Cost.RealTransposePreserve
