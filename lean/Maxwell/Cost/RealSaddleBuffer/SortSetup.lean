import Maxwell.Cost.RealSaddleBuffer.Correctness
import Maxwell.Cost.RealSparseOrder.SortState

namespace Maxwell.Cost.RealSaddleBuffer
open RealSparseOrder (Buffer Stored)
open RealSimulation.Control
open RealSparse (execute execute_sound)
set_option maxRecDepth 20000
set_option maxHeartbeats 1600000

/-- Charged setup of the generic in-memory sort. Metadata78/79 contains
the second sorting buffer;52/53 retain the source dimension/entry count. -/
def sortSetup : Machine := ⟨[
  .indexLiteral 0 0, .indexLiteral 1 1, .indexLiteral 2 2,
  .indexAdd 26 73 73, .indexAdd 26 26 70, .indexAdd 26 26 72,
  .indexCopy 27 76, .indexCopy 28 77, .indexCopy 29 78, .indexCopy 30 79,
  .indexLiteral 18 1, .indexAdd 52 70 71, .indexAdd 52 52 72, .indexCopy 53 26, .halt]⟩

def sortPrepared (s : Store) : Store :=
  let t := s.val.setIndex 0 0
  let t := t.setIndex 1 1
  let t := t.setIndex 2 2
  let t := t.setIndex 26 (s.val.indices 73 + s.val.indices 73)
  let t := t.setIndex 26 (s.val.indices 73 + s.val.indices 73 + s.val.indices 70)
  let t := t.setIndex 26 (s.val.indices 73 + s.val.indices 73 + s.val.indices 70 + s.val.indices 72)
  let t := t.setIndex 27 (s.val.indices 76)
  let t := t.setIndex 28 (s.val.indices 77)
  let t := t.setIndex 29 (s.val.indices 78)
  let t := t.setIndex 30 (s.val.indices 79)
  let t := t.setIndex 18 1
  let t := t.setIndex 52 (s.val.indices 70 + s.val.indices 71)
  let t := t.setIndex 52 (s.val.indices 70 + s.val.indices 71 + s.val.indices 72)
  Store.ofState (t.setIndex 53 (s.val.indices 73 + s.val.indices 73 + s.val.indices 70 + s.val.indices 72))

theorem sortSetup_executes (input : RAMInput) (tape : ℕ → Bool) (s : Store) :
    Executes input tape (.call sortSetup) 15 s (sortPrepared s) := by
  apply Executes.call _ _ _ 14
  · apply execute_sound
    simp [execute, sortSetup, Machine.next, s.property, RAMState.setIndex]
  · simp [sortSetup, RAMState.setIndex, s.property]

theorem sortPrepared_index (s : Store) (i : ℕ) (hi : 100 ≤ i) :
    (sortPrepared s).val.indices i = s.val.indices i := by
  have hsmall : ∀ j < 100, i ≠ j := by omega
  simp [sortPrepared, Store.ofState, RAMState.setIndex, hsmall]

theorem sortPrepared_invariant (dst spare : Buffer) (rows columns padding : ℕ)
    (es : List SparseEntry) (s : Store) (hdst : dst.Safe) (hspare : spare.Safe)
    (hsep : RealSparseOrder.Separated dst (RealSaddle.entries rows columns padding es).length
      spare (RealSaddle.entries rows columns padding es).length)
    (hstored : Stored dst s.val (RealSaddle.entries rows columns padding es))
    (hr : s.val.indices 70 = rows) (hc : s.val.indices 71 = columns)
    (hp : s.val.indices 72 = padding) (hm : s.val.indices 73 = es.length)
    (hdc : s.val.indices 76 = dst.coordinates) (hdv : s.val.indices 77 = dst.coefficients)
    (hsc : s.val.indices 78 = spare.coordinates) (hsv : s.val.indices 79 = spare.coefficients) :
    RealSparseOrder.Sort.Invariant (sortPrepared s).val dst spare 1
      (RealSparseOrder.singletonRuns (RealSaddle.entries rows columns padding es)) ∧
      (sortPrepared s).val.indices 52 = rows + columns + padding ∧
      (sortPrepared s).val.indices 53 = rows + 2 * es.length + padding := by
  refine ⟨⟨?_, hdst, hspare, ?_, by simpa using hsep⟩, ?_, ?_⟩
  · constructor <;> simp [sortPrepared, Store.ofState, RAMState.setIndex, hr, hp, hm, hdc, hdv, hsc, hsv,
      RealSaddle.entries_length, Nat.add_comm, two_mul]
  · rw [RealSparseOrder.singletonRuns_flatten, RealSparseOrder.records_stored]
    intro j hj
    obtain ⟨hrow, hcol, hval⟩ := hstored j hj
    exact ⟨(sortPrepared_index s (dst.row j) (by dsimp [Buffer.row]; exact le_add_of_le_left hdst.2)).trans hrow,
      (sortPrepared_index s (dst.column j) (by have := hdst.2; dsimp [Buffer.column]; omega)).trans hcol, hval⟩
  · simp [sortPrepared, Store.ofState, RAMState.setIndex, hr, hc, hp]
  · simp [sortPrepared, Store.ofState, RAMState.setIndex, hr, hm, hp, two_mul, Nat.add_comm, Nat.add_left_comm]

end Maxwell.Cost.RealSaddleBuffer
