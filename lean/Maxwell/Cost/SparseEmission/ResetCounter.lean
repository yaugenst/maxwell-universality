import Maxwell.Cost.WordReset
import Maxwell.Cost.SourceCircuit.Common

namespace Maxwell.Cost.SparseEmission.ResetCounter
open Structured

def code : Code := .seq (WordCall.resetStart 113) (.call (WordTransfer.clone 115 113))

theorem executes (input : List Bool) (randomTape : ℕ → Bool)
    (oldWord word : List Bool) (origin cacheOrigin : ℤ) (s : Store)
    (hrow : s.val.tapes 113 = BitTape.shifted oldWord origin)
    (hcache : s.val.tapes 115 = BitTape.shifted word cacheOrigin) :
    ∃ t, Executes input randomTape code (11*oldWord.length+15*word.length+27) s t ∧
      t.val.tapes 113 = BitTape.shifted word origin ∧
      t.val.address = s.val.address ∧ t.val.memory = s.val.memory ∧
      SourceCircuit.Frame {113} s.val t.val ∧
      (∀ i, i ≠ 113 → t.val.tapes i = s.val.tapes i) := by
  obtain ⟨a,ea,aTapes,af⟩ := WordCall.reset_start 113 input randomTape oldWord origin s hrow
  obtain ⟨t,et,tt,tf⟩ := WordCall.clone 115 113 (by decide) input randomTape word cacheOrigin origin a
    (by simpa [aTapes] using hcache) (by simp [aTapes])
  have keep (i : ℕ) (hi : i ≠ 113) : t.val.tapes i = s.val.tapes i := by simp [tt,aTapes,hi]
  have aFrame : SourceCircuit.Frame {113} s.val a.val := SourceCircuit.frame_transfer af (by
    intro i hi
    simp only [Finset.mem_singleton] at hi
    simp [aTapes,hi])
  have tFrame : SourceCircuit.Frame {113} a.val t.val := SourceCircuit.frame_transfer tf (by
    intro i hi
    simp only [Finset.mem_singleton] at hi
    simp [tt,hi])
  refine ⟨t,?_,by simp [tt],tf.1.trans af.1,tf.2.2.1.trans af.2.2.1,aFrame.trans tFrame,keep⟩
  convert ea.seq et using 1 <;> first | rfl | omega

end Maxwell.Cost.SparseEmission.ResetCounter
