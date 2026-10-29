import Maxwell.Cost.SourceCircuit.Common
import Maxwell.Cost.WordCall

namespace Maxwell.Cost.SourceCircuit
open Structured
open RationalAccumulator (Blank)

def replaceCode (source target : ℕ) : Code :=
  .seq (.call (TapeOps.clear target)) (.call (WordTransfer.move source target))

theorem replace_executes (source target : ℕ) (hne : source ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (word old : List Bool) (s : Store)
    (hs : BankArray.Word s.val source word) (ht : BankArray.Word s.val target old) :
    ∃ t, Executes input tape (replaceCode source target) (6*old.length+12*word.length+15) s t ∧
      BankArray.Word t.val target word ∧ Blank t.val source ∧
      t.val.memory = s.val.memory ∧ Frame {source,target} s.val t.val ∧
      (∀ j, j ≠ source → j ≠ target → t.val.tapes j = s.val.tapes j) := by
  obtain ⟨so,hs⟩ := hs
  obtain ⟨oldOrigin,ht⟩ := ht
  obtain ⟨c,ec,ct,cf⟩ := WordCall.clear target input tape old oldOrigin s ht
  obtain ⟨t,et,tp,ts,tt,tf⟩ := WordTransfer.move_steps source target hne input tape word so
    (oldOrigin+old.length) c.val c.property (by simpa [ct,hne] using hs) (by simp [ct])
  have em : Executes input tape (.call (WordTransfer.move source target)) (12*word.length+11)
      c (Store.ofState t) := .call _ c t _ et (by rw [tp]; rfl)
  have keep (j : ℕ) (hjs : j ≠ source) (hjt : j ≠ target) : t.tapes j = s.val.tapes j := by
    rw [tf.2.2.2.2.2.1 j hjs hjt]
    simp [ct,hjt]
  have cf' : WordTransfer.Frame source target s.val c.val :=
    ⟨cf.1,cf.2.1,cf.2.2.1,cf.2.2.2.1,cf.2.2.2.2.1,
      fun j _ hjt => cf.2.2.2.2.2.1 j hjt hjt,
      fun j _ _ h26 h27 => cf.2.2.2.2.2.2 j h26 h27⟩
  refine ⟨Store.ofState t,?_,⟨oldOrigin+old.length,tt⟩,⟨so+word.length,ts⟩,
    tf.2.2.1.trans cf.2.2.1,frame_transfer (cf'.trans tf) ?_,keep⟩
  · convert ec.seq em using 1 <;> first | rfl | omega
  · intro j hj
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hj
    exact keep j hj.1 hj.2

end Maxwell.Cost.SourceCircuit
