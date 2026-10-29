import Maxwell.Cost.SourceCircuit.Common
import Maxwell.Cost.WordCall

namespace Maxwell.Cost.CalibrationMatrix

open Structured BankArray

/-- Copy the operand, increment the copy, and return it to its first cell. -/
def successorWordCode (source target : ℕ) : Code :=
  .seq (.call (WordTransfer.clone source target)) (incrementCode target)

/-- The successor is a raw binary word, including any high padding already
present in the operand. It needs at most one additional bit. -/
theorem successor_word_bank (source target : ℕ) (htarget : 10 ≤ target)
    (hne : source ≠ target) (input : List Bool) (randomTape : ℕ → Bool)
    (word : List Bool) (s : Store) (hw : Word s.val source word)
    (ht : RationalAccumulator.Blank s.val target) (hscratch : Scratch s.val) :
    ∃ cost t, cost ≤ 27*word.length+35 ∧
      Executes input randomTape (successorWordCode source target) cost s t ∧
      Word t.val target (Increment.bits word) ∧ Word t.val source word ∧
      addressValue (Increment.bits word) = addressValue word+1 ∧
      (Increment.bits word).length ≤ word.length+1 ∧ Scratch t.val ∧
      t.val.memory = s.val.memory ∧ t.val.address = s.val.address ∧
      (∀ i, i ≠ target → t.val.tapes i = s.val.tapes i) ∧ FrameExcept target s.val t.val := by
  obtain ⟨so, hsource⟩ := hw
  obtain ⟨targetOrigin, hblank⟩ := ht
  obtain ⟨a, ea, hatapes, haf⟩ := WordCall.clone source target hne input randomTape
    word so targetOrigin s hsource hblank
  have akeep (i : ℕ) (hi : i ≠ target) : a.val.tapes i = s.val.tapes i := by
    simp [hatapes, hi]
  have ascratch : Scratch a.val :=
    SourceCircuit.scratch_of_tapes hscratch (fun i hi => akeep i (by omega))
  have aword : Word a.val target word := ⟨targetOrigin, by simp [hatapes]⟩
  obtain ⟨cost, t, hcost, et, hword, hts, htm, hta, htapes, htf⟩ :=
    increment_bank target htarget input randomTape word a aword ascratch
  have keep (i : ℕ) (hi : i ≠ target) : t.val.tapes i = s.val.tapes i :=
    (htapes i hi).trans (akeep i hi)
  refine ⟨15*word.length+17+cost, t, by omega, ea.seq et, hword,
    ⟨so, (keep source hne).trans hsource⟩, Increment.bits_value word,
    Increment.bits_length_le word, hts, htm.trans haf.2.2.1, hta.trans haf.1, keep, ?_⟩
  refine ⟨htf.1.trans haf.2.1, htf.2.1.trans haf.2.2.2.1,
    htf.2.2.1.trans haf.2.2.2.2.1, fun i _ hi => keep i hi, ?_⟩
  intro i hi h24 h25 h26 h27 h28 h29
  exact (htf.2.2.2.2 i hi h24 h25 h26 h27 h28 h29).trans
    (haf.2.2.2.2.2.2 i h24 h25 h26 h27)

end Maxwell.Cost.CalibrationMatrix
