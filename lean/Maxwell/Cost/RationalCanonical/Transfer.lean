import Maxwell.Cost.RationalAccumulator.Bank

namespace Maxwell.Cost.RationalCanonical
open Structured RationalAccumulator

theorem clear_word (i a : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (s : Store) (ha : Word s.val i a) :
    ∃ t : Store, Executes input tape (.call (TapeOps.clear i)) (6*a.bits.length+4) s t ∧
      Word t.val i 0 ∧ WordTransfer.Frame i i s.val t.val := by
  obtain ⟨origin, hw⟩ := ha
  obtain ⟨t, he, hp, hc, hf⟩ := TapeOps.clear_steps i input tape a.bits origin s.val s.property hw
  exact ⟨Store.ofState t, Executes.call _ _ _ _ he (by simp [TapeOps.clear,hp]),
    (zero_word_iff_blank _ _).mpr ⟨_,hc⟩, WordTransfer.frame_of_copy hf⟩

theorem move_word (source target a : ℕ) (hne : source ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (ha : Word s.val source a) (hz : Word s.val target 0) :
    ∃ t : Store, Executes input tape (.call (WordTransfer.move source target))
      (12*a.bits.length+11) s t ∧ Word t.val source 0 ∧ Word t.val target a ∧
      WordTransfer.Frame source target s.val t.val := by
  obtain ⟨so, hs⟩ := ha
  obtain ⟨destOrigin, ht⟩ := (zero_word_iff_blank _ _).mp hz
  obtain ⟨t, he, hp, hs', ht', hf⟩ :=
    WordTransfer.move_steps source target hne input tape a.bits so destOrigin s.val s.property hs ht
  exact ⟨Store.ofState t, Executes.call _ _ _ _ he (by simp [WordTransfer.move, TapeOps.copyClear, Rewind.program, BitRAMInstruction.relocate, hp]),
    (zero_word_iff_blank _ _).mpr ⟨_,hs'⟩, ⟨_,ht'⟩, hf⟩

theorem clone_word (source target a : ℕ) (hne : source ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (ha : Word s.val source a) (hz : Word s.val target 0) :
    ∃ t : Store, Executes input tape (.call (WordTransfer.clone source target))
      (15*a.bits.length+17) s t ∧ Word t.val source a ∧ Word t.val target a ∧
      WordTransfer.Frame source target s.val t.val := by
  obtain ⟨so, hs⟩ := ha
  obtain ⟨destOrigin, ht⟩ := (zero_word_iff_blank _ _).mp hz
  obtain ⟨t, he, hp, hs', ht', hf⟩ :=
    WordTransfer.clone_steps source target hne input tape a.bits so destOrigin s.val s.property hs ht
  exact ⟨Store.ofState t, Executes.call _ _ _ _ he (by simp [WordTransfer.clone, Copy.program, Rewind.program, BitRAMInstruction.relocate, hp]),
    ⟨_,hs'⟩, ⟨_,ht'⟩, hf⟩

end Maxwell.Cost.RationalCanonical
