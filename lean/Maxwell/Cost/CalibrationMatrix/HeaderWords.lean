import Maxwell.Cost.CalibrationMatrix.PadWord
import Maxwell.Cost.CalibrationMatrix.WordMove

/-! Word operations with the exact frames used by material-header assembly. -/
namespace Maxwell.Cost.CalibrationMatrix.HeaderWords
open Structured BankArray
open RationalAccumulator (Blank)

theorem pad_raw (source clock target : ℕ) (hsc : source ≠ clock) (hst : source ≠ target)
    (hct : clock ≠ target) (input : List Bool) (tape : ℕ → Bool)
    (width : ℕ) (clockWord word : List Bool) (hclock : clockWord.length = width)
    (s : Store) (hs : Word s.val source word)
    (hc : Word s.val clock clockWord) (ht : Blank s.val target) :
    ∃ cost t, cost ≤ 20*width+12 ∧
      Executes input tape (padWordCode source clock target) cost s t ∧
      Word t.val target (FixedWidth.bits width word) ∧
      BinaryPrecision.Frame {target} s.val t.val := by
  obtain ⟨so,hs⟩ := hs
  obtain ⟨co,hc⟩ := hc
  obtain ⟨ot,ht⟩ := ht
  obtain ⟨cost,t,hcost,he,hw,_,_,hf⟩ := pad_word_raw source clock target hsc hst hct
    input tape width clockWord word hclock so co ot s hs hc ht
  exact ⟨cost,t,hcost,he,⟨ot,hw⟩,
    ⟨hf.address,hf.inputHead,hf.memory,hf.randomCursor,hf.output,
      fun i hi => hf.tapes i (by simpa using hi)⟩⟩

theorem pad (source clock target : ℕ) (hsc : source ≠ clock) (hst : source ≠ target)
    (hct : clock ≠ target) (input : List Bool) (tape : ℕ → Bool)
    (width : ℕ) (clockWord word : List Bool) (hclock : clockWord.length = width)
    (hfit : word.length ≤ width) (s : Store) (hs : Word s.val source word)
    (hc : Word s.val clock clockWord) (ht : Blank s.val target) :
    ∃ cost t, cost ≤ 20*width+12 ∧
      Executes input tape (padWordCode source clock target) cost s t ∧
      Word t.val target (FixedWidth.bits width word) ∧
      BinaryPrecision.Frame {target} s.val t.val := by
  obtain ⟨so,hs⟩ := hs
  obtain ⟨co,hc⟩ := hc
  obtain ⟨ot,ht⟩ := ht
  obtain ⟨cost,t,hcost,he,hw,_,_,_,hf⟩ := pad_word source clock target hsc hst hct
    input tape width clockWord word hclock hfit so co ot s hs hc ht
  exact ⟨cost,t,hcost,he,⟨ot,hw⟩,
    ⟨hf.address,hf.inputHead,hf.memory,hf.randomCursor,hf.output,
      fun i hi => hf.tapes i (by simpa using hi)⟩⟩

theorem append (source target : ℕ) (hne : source ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (word preceding : List Bool)
    (origin : ℤ) (s : Store) (hs : Word s.val source word)
    (ht : s.val.tapes target = BitTape.shiftedEnd preceding origin) :
    ∃ t, Executes input tape (.call (TapeOps.copyClear source target))
        (8*word.length+4) s t ∧ Blank t.val source ∧
      t.val.tapes target = BitTape.shiftedEnd (preceding ++ word) origin ∧
      BinaryPrecision.Frame {source,target} s.val t.val := by
  obtain ⟨so,hs⟩ := hs
  obtain ⟨t,he,hb,hw,hf,_⟩ := append_word source target hne input tape word preceding so origin s hs ht
  exact ⟨t,he,hb,hw,hf⟩

theorem rewind (target : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (word : List Bool) (origin : ℤ) (s : Store)
    (hw : s.val.tapes target = BitTape.shiftedEnd word origin) :
    ∃ t, Executes input tape (.call (Rewind.program target)) (4*word.length+6) s t ∧
      t.val.tapes target = BitTape.shifted word origin ∧
      BinaryPrecision.Frame {target} s.val t.val := by
  have hr := WordTransfer.rewind_shifted target origin input tape word s.val s.property hw
  let t := Store.ofState (Rewind.finishAt target origin s.val)
  refine ⟨t,.call _ s _ _ hr.1 (by simp [Rewind.program,Rewind.finishAt]),hr.2,?_⟩
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_⟩
  intro i hi
  have hi' : i ≠ target := by simpa using hi
  simp [t,Store.ofState,Rewind.finishAt,hi']

theorem clear (target : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (word : List Bool) (s : Store) (hw : Word s.val target word) :
    ∃ t, Executes input tape (.call (TapeOps.clear target)) (6*word.length+4) s t ∧
      Blank t.val target ∧ BinaryPrecision.Frame {target} s.val t.val := by
  obtain ⟨origin,hw⟩ := hw
  obtain ⟨t,he,ht,hf⟩ := WordCall.clear target input tape word origin s hw
  refine ⟨t,he,⟨origin+word.length,by simp [ht]⟩,
    ⟨hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2.1,?_⟩⟩
  intro i hi
  have hi' : i ≠ target := by simpa using hi
  simp [ht,hi']

end Maxwell.Cost.CalibrationMatrix.HeaderWords

namespace Maxwell.Cost.BinaryPrecision
open BankArray
open RationalAccumulator (Blank)

theorem Frame.word {a : Finset ℕ} {s t : BitRAMState}
    (h : BinaryPrecision.Frame a s t) {i : ℕ} (hi : i ∉ a) {w : List Bool}
    (hw : Word s i w) : Word t i w := word_of_eq (h.tapes i hi) hw

theorem Frame.blank {a : Finset ℕ} {s t : BitRAMState}
    (h : BinaryPrecision.Frame a s t) {i : ℕ} (hi : i ∉ a) (hw : Blank s i) : Blank t i :=
  RationalAccumulator.blank_of_eq (h.tapes i hi) hw

end Maxwell.Cost.BinaryPrecision
