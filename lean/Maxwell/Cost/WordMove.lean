import Maxwell.Cost.WordCall

namespace Maxwell.Cost.WordCall
open Structured

def moveEnd (source target : ℕ) : Code :=
  .seq (.call (Rewind.program source)) (.call (WordTransfer.move source target))

/-- Move a completed word into a persistent bank, restoring its new head to
its first cell and clearing every source cell by actual tape operations. -/
theorem move_end (source target : ℕ) (hne : source ≠ target)
    (input : List Bool) (randomTape : ℕ → Bool) (word : List Bool)
    (origin targetOrigin : ℤ) (s : Store)
    (hs : s.val.tapes source = BitTape.shiftedEnd word origin)
    (ht : s.val.tapes target = {BitTape.blank with head := targetOrigin}) :
    ∃ t, Executes input randomTape (moveEnd source target) (16 * word.length + 17) s t ∧
      t.val.tapes = Function.update (Function.update s.val.tapes
        source {BitTape.blank with head := origin + word.length})
        target (BitTape.shifted word targetOrigin) ∧ WordTransfer.Frame source target s.val t.val := by
  have hr := WordTransfer.rewind_shifted source origin input randomTape word s.val s.property hs
  let middle := Store.ofState (Rewind.finishAt source origin s.val)
  have er : Executes input randomTape (.call (Rewind.program source)) (4 * word.length + 6) s middle :=
    .call _ s _ _ hr.1 (by simp [Rewind.program, Rewind.finishAt])
  obtain ⟨t, et, hp, htSource, htTarget, hf⟩ := WordTransfer.move_steps source target hne
    input randomTape word origin targetOrigin middle.val middle.property hr.2
    (by simpa [middle, Store.ofState, Rewind.finishAt, Ne.symm hne] using ht)
  have em : Executes input randomTape (.call (WordTransfer.move source target))
      (12 * word.length + 11) middle (Store.ofState t) :=
    .call _ middle t _ et (by
      simp [WordTransfer.move, hp, TapeOps.copyClear, Rewind.program, BitRAMInstruction.relocate])
  refine ⟨Store.ofState t, ?_, ?_,
    (WordTransfer.frame_rewind source target source (Or.inl rfl) origin s.val).trans hf⟩
  · convert er.seq em using 1 <;> first | rfl | omega
  · funext i
    by_cases hit : i = target
    · subst i; simpa [Store.ofState] using htTarget
    · by_cases his : i = source
      · subst i; simpa [Store.ofState, hne] using htSource
      · simpa [Store.ofState, middle, Rewind.finishAt, his, hit] using
          hf.2.2.2.2.2.1 i his hit

end Maxwell.Cost.WordCall
