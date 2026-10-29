import Maxwell.Cost.WordTransfer
import Maxwell.Cost.Structured.Primitive

namespace Maxwell.Cost.WordCall
open Structured

/-- Exact global tape-update form of the existing finite clone routine. -/
theorem clone (source target : ℕ) (hne : source ≠ target)
    (input : List Bool) (randomTape : ℕ → Bool) (word : List Bool) (so targetOrigin : ℤ)
    (s : Store) (hs : s.val.tapes source = BitTape.shifted word so)
    (ht : s.val.tapes target = {BitTape.blank with head := targetOrigin}) :
    ∃ t, Executes input randomTape (.call (WordTransfer.clone source target))
        (15 * word.length + 17) s t ∧
      t.val.tapes = Function.update s.val.tapes target (BitTape.shifted word targetOrigin) ∧
      WordTransfer.Frame source target s.val t.val := by
  obtain ⟨t, he, hp, hsource, htarget, hf⟩ := WordTransfer.clone_steps
    source target hne input randomTape word so targetOrigin s.val s.property hs ht
  refine ⟨Store.ofState t, ?_, ?_, hf⟩
  · simpa using Executes.call _ s t _ he (by rw [hp]; rfl)
  · funext i
    by_cases hit : i = target
    · subst i; simpa [Store.ofState] using htarget
    · by_cases his : i = source
      · subst i; simpa [Store.ofState, hne] using hsource.trans hs.symm
      · simpa [Store.ofState, hit] using hf.2.2.2.2.2.1 i his hit

/-- Clear consumes a word at its first cell and preserves every other tape. -/
theorem clear (target : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (word : List Bool) (origin : ℤ) (s : Store)
    (ht : s.val.tapes target = BitTape.shifted word origin) :
    ∃ t, Executes input randomTape (.call (TapeOps.clear target)) (6 * word.length + 4) s t ∧
      t.val.tapes = Function.update s.val.tapes target
        {BitTape.blank with head := origin + word.length} ∧ TapeOps.Frame target target s.val t.val := by
  obtain ⟨t, he, hp, htarget, hf⟩ :=
    TapeOps.clear_steps target input randomTape word origin s.val s.property ht
  refine ⟨Store.ofState t, ?_, ?_, hf⟩
  · simpa using Executes.call _ s t _ he (by rw [hp]; rfl)
  · funext i
    by_cases hi : i = target
    · subst i; simpa [Store.ofState] using htarget
    · simpa [Store.ofState, hi] using hf.2.2.2.2.2.1 i hi hi

def eraseEnd (target : ℕ) : Code :=
  .seq (.call (Rewind.program target)) (.call (TapeOps.clear target))

theorem erase_end (target : ℕ) (input : List Bool) (randomTape : ℕ → Bool)
    (word : List Bool) (origin : ℤ) (s : Store)
    (ht : s.val.tapes target = BitTape.shiftedEnd word origin) :
    ∃ t, Executes input randomTape (eraseEnd target) (10 * word.length + 10) s t ∧
      t.val.tapes = Function.update s.val.tapes target
        {BitTape.blank with head := origin + word.length} ∧ WordTransfer.Frame target target s.val t.val := by
  have hr := WordTransfer.rewind_shifted target origin input randomTape word s.val s.property ht
  let middle := Store.ofState (Rewind.finishAt target origin s.val)
  have er : Executes input randomTape (.call (Rewind.program target)) (4 * word.length + 6) s middle :=
    .call _ s _ _ hr.1 (by simp [Rewind.program, Rewind.finishAt])
  obtain ⟨t, et, htapes, hf⟩ := clear target input randomTape word origin middle hr.2
  refine ⟨t, ?_, ?_, (WordTransfer.frame_rewind target target target (Or.inl rfl)
    origin s.val).trans (WordTransfer.frame_of_copy hf)⟩
  · convert er.seq et using 1 <;> first | rfl | omega
  · rw [htapes]
    simp [middle, Store.ofState, Rewind.finishAt]

end Maxwell.Cost.WordCall
