import Maxwell.Cost.RealSaddleBuffer.SortSetup

namespace Maxwell.Cost.RealSaddleBuffer
open RealSimulation.Control
open RealSparse (execute execute_sound)
open RealSparseOrder (Buffer)
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

/-- Caller data is the actual relabeling result: count26, source coordinate
base27, coefficient base28, active-row count35, and column count42. -/
def layoutSetup : Machine := ⟨[
  .indexCopy 70 35, .indexCopy 71 42, .indexCopy 72 26, .indexCopy 73 26,
  .indexCopy 74 27, .indexCopy 75 28, .indexLiteral 58 100,
  .indexAdd 59 26 26, .indexAdd 60 59 59, .indexAdd 61 60 60,
  .indexAdd 76 58 61, .indexCopy 77 76, .indexAdd 62 61 60,
  .indexAdd 79 58 62, .indexAdd 63 61 61, .indexAdd 78 58 63,
  .indexAdd 64 63 61, .indexAdd 54 58 64, .indexAdd 65 60 59,
  .indexAdd 80 58 65, .halt]⟩

def layoutPrepared (s : Store) : Store :=
  let m := s.val.indices 26
  let t := s.val.setIndex 70 (s.val.indices 35)
  let t := t.setIndex 71 (s.val.indices 42)
  let t := t.setIndex 72 m
  let t := t.setIndex 73 m
  let t := t.setIndex 74 (s.val.indices 27)
  let t := t.setIndex 75 (s.val.indices 28)
  let t := t.setIndex 58 100
  let t := t.setIndex 59 (m + m)
  let t := t.setIndex 60 ((m + m) + (m + m))
  let t := t.setIndex 61 (8 * m)
  let t := t.setIndex 76 (100 + 8 * m)
  let t := t.setIndex 77 (100 + 8 * m)
  let t := t.setIndex 62 (12 * m)
  let t := t.setIndex 79 (100 + 12 * m)
  let t := t.setIndex 63 (16 * m)
  let t := t.setIndex 78 (100 + 16 * m)
  let t := t.setIndex 64 (24 * m)
  let t := t.setIndex 54 (100 + 24 * m)
  let t := t.setIndex 65 (6 * m)
  Store.ofState (t.setIndex 80 (100 + 6 * m))

def saddleBuffer (m : ℕ) : Buffer := ⟨100 + 8 * m, 100 + 8 * m⟩
def saddleSpare (m : ℕ) : Buffer := ⟨100 + 12 * m, 100 + 16 * m⟩

theorem layoutSetup_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store) :
    Executes input tape (.call layoutSetup) 21 s (layoutPrepared s) := by
  apply Executes.call _ _ _ 20
  · apply execute_sound
    simp (config := { maxSteps := 1000000 }) [execute, layoutSetup, Machine.next, s.property, RAMState.setIndex,
      show 8 * s.val.indices 26 = ((s.val.indices 26 + s.val.indices 26) +
        (s.val.indices 26 + s.val.indices 26)) + ((s.val.indices 26 + s.val.indices 26) +
        (s.val.indices 26 + s.val.indices 26)) by omega]
    congr 1 <;> omega
  · simp [layoutSetup, RAMState.setIndex, s.property]

theorem layoutPrepared_words (s : Store) : (layoutPrepared s).val.words = s.val.words := rfl

theorem layoutPrepared_index (s : Store) (i : ℕ) (hi : 100 ≤ i) :
    (layoutPrepared s).val.indices i = s.val.indices i := by
  have hsmall : ∀ j < 100, i ≠ j := by omega
  simp [layoutPrepared, Store.ofState, RAMState.setIndex, hsmall]

theorem layoutPrepared_metadata (s : Store) (m rows columns : ℕ)
    (hm : s.val.indices 26 = m) (hr : s.val.indices 35 = rows) (hc : s.val.indices 42 = columns) :
    (layoutPrepared s).val.indices 70 = rows ∧ (layoutPrepared s).val.indices 71 = columns ∧
    (layoutPrepared s).val.indices 72 = m ∧ (layoutPrepared s).val.indices 73 = m ∧
    (layoutPrepared s).val.indices 74 = s.val.indices 27 ∧
    (layoutPrepared s).val.indices 75 = s.val.indices 28 ∧
    (layoutPrepared s).val.indices 76 = (saddleBuffer m).coordinates ∧
    (layoutPrepared s).val.indices 77 = (saddleBuffer m).coefficients ∧
    (layoutPrepared s).val.indices 78 = (saddleSpare m).coordinates ∧
    (layoutPrepared s).val.indices 79 = (saddleSpare m).coefficients ∧
    (layoutPrepared s).val.indices 80 = 100 + 6 * m ∧
    (layoutPrepared s).val.indices 54 = 100 + 24 * m := by
  simp [layoutPrepared, Store.ofState, RAMState.setIndex, hm, hr, hc, saddleBuffer, saddleSpare]

theorem saddle_separated (m rows : ℕ) (hr : rows ≤ m) :
    RealSparseOrder.Separated (saddleBuffer m) (3 * m + rows)
      (saddleSpare m) (3 * m + rows) := by
  constructor <;> left <;> dsimp [saddleBuffer, saddleSpare] <;> omega

end Maxwell.Cost.RealSaddleBuffer
