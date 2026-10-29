import Maxwell.Cost.BinaryPrecision
import Maxwell.Cost.WordCall
import Maxwell.Cost.RationalAccumulator.Bank

namespace Maxwell.Cost.CalibrationMatrix
open Structured

/-- An actual destructive word transfer, including its final rewind, with
an exact global tape update for composing finite register-bank schedules. -/
theorem move_word (source target : ℕ) (hne : source ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (word : List Bool) (so targetOrigin : ℤ)
    (s : Store) (hs : s.val.tapes source = BitTape.shifted word so)
    (ht : s.val.tapes target = {BitTape.blank with head := targetOrigin}) :
    ∃ t, Executes input tape (.call (WordTransfer.move source target))
        (12 * word.length + 11) s t ∧
      t.val.tapes = Function.update (Function.update s.val.tapes source
        {BitTape.blank with head := so + word.length}) target (BitTape.shifted word targetOrigin) ∧
      BinaryPrecision.Frame {source, target} s.val t.val ∧
      (∀ i, i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → t.val.registers i = s.val.registers i) := by
  obtain ⟨t, he, hp, hs', ht', hf⟩ := WordTransfer.move_steps source target hne
    input tape word so targetOrigin s.val s.property hs ht
  refine ⟨Store.ofState t, ?_, ?_, ?_, hf.2.2.2.2.2.2⟩
  · exact .call _ s t _ he (by
      simp [WordTransfer.move, hp, TapeOps.copyClear, Rewind.program, BitRAMInstruction.relocate])
  · funext i
    by_cases hit : i = target
    · subst i; simpa [Store.ofState] using ht'
    · by_cases his : i = source
      · subst i; simpa [Store.ofState, hne] using hs'
      · simpa [Store.ofState, hit, his] using hf.2.2.2.2.2.1 i his hit
  · refine ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, ?_⟩
    intro i hi
    have h : i ≠ source ∧ i ≠ target := by simpa using hi
    exact hf.2.2.2.2.2.1 i h.1 h.2

/-- Append a raw word at the current end of another tape and consume the
source. Independent origins permit repeated reuse of the emptied workspace. -/
theorem append_word (source target : ℕ) (hne : source ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (word preceding : List Bool)
    (so targetOrigin : ℤ) (s : Store)
    (hs : s.val.tapes source = BitTape.shifted word so)
    (ht : s.val.tapes target = BitTape.shiftedEnd preceding targetOrigin) :
    ∃ t, Executes input tape (.call (TapeOps.copyClear source target))
        (8*word.length+4) s t ∧
      RationalAccumulator.Blank t.val source ∧
      t.val.tapes target = BitTape.shiftedEnd (preceding ++ word) targetOrigin ∧
      BinaryPrecision.Frame {source, target} s.val t.val ∧
      (∀ i, i ≠ 26 → i ≠ 27 → t.val.registers i = s.val.registers i) := by
  obtain ⟨t, he, hp, hs', ht', hf⟩ := TapeOps.copyClear_shifted_steps
    source target hne input tape word preceding so targetOrigin s.val s.property hs ht
  refine ⟨Store.ofState t, ?_, ⟨so+word.length, hs'⟩, ht', ?_, hf.2.2.2.2.2.2⟩
  · exact .call _ s t _ he (by simp [TapeOps.copyClear, hp])
  · refine ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, ?_⟩
    intro i hi
    have h : i ≠ source ∧ i ≠ target := by simpa using hi
    exact hf.2.2.2.2.2.1 i h.1 h.2

end Maxwell.Cost.CalibrationMatrix
