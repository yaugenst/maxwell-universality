import Maxwell.Cost.TapeResetShifted
import Maxwell.Cost.ScanForward
import Maxwell.Cost.WordCall

namespace Maxwell.Cost.WordCall
open Structured

def resetStart (target : ℕ) : Code :=
  .seq (.call (ScanForward.program target)) (.call (TapeReset.program target))

/-- Erase a word while restoring its original head position; no head reset is
performed by the host. This permits immediate reuse by a sequential parser. -/
theorem reset_start (target : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (word : List Bool) (origin : ℤ) (s : Store)
    (ht : s.val.tapes target = BitTape.shifted word origin) :
    ∃ t, Executes input randomTape (resetStart target) (11 * word.length + 10) s t ∧
      t.val.tapes = Function.update s.val.tapes target {BitTape.blank with head := origin} ∧
      WordTransfer.Frame target target s.val t.val := by
  obtain ⟨hs, hh, hf⟩ := ScanForward.shifted_steps target origin input randomTape word s.val s.property ht
  let middle := Store.ofState (ScanForward.finish target word.length s.val)
  have es : Executes input randomTape (.call (ScanForward.program target)) (5 * word.length + 4) s middle :=
    .call _ s _ _ hs (by simp [ScanForward.program, ScanForward.finish])
  have hr := TapeReset.shifted_steps target origin input randomTape word middle.val middle.property hh
  let finalState := TapeReset.finishAt target origin middle.val
  have er : Executes input randomTape (.call (TapeReset.program target)) (6 * word.length + 6)
      middle (Store.ofState finalState) :=
    .call _ middle _ _ hr (by simp [TapeReset.program, finalState, TapeReset.finishAt])
  refine ⟨Store.ofState finalState, ?_, ?_,
    (WordTransfer.frame_of_copy hf).trans
      (WordTransfer.frame_of_copy (TapeReset.finishAt_frame target origin middle.val))⟩
  · convert es.seq er using 1 <;> first | rfl | omega
  · simp [finalState, middle, Store.ofState, TapeReset.finishAt, ScanForward.finish]

end Maxwell.Cost.WordCall
