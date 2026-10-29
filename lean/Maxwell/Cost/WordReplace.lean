import Maxwell.Cost.BankArray.Common

namespace Maxwell.Cost.WordReplace
open Structured
open BankArray (Word)

def code (source target : ℕ) : Code := .seq (.call (TapeOps.clear target)) (.call (WordTransfer.clone source target))

def Frame (target : ℕ) (s t : BitRAMState) : Prop :=
  t.address=s.address ∧ t.inputHead=s.inputHead ∧ t.memory=s.memory ∧
  t.randomCursor=s.randomCursor ∧ t.output=s.output ∧
  (∀ i, i≠target → t.tapes i=s.tapes i) ∧
  (∀ i, i≠24 → i≠25 → i≠26 → i≠27 → t.registers i=s.registers i)

theorem executes (source target : ℕ) (hne : source≠target)
    (input : List Bool) (tape : ℕ → Bool) (xs ys : List Bool) (s : Store)
    (hs : Word s.val source xs) (ht : Word s.val target ys) :
    ∃ t, Executes input tape (code source target) (6*ys.length+15*xs.length+21) s t ∧
      Word t.val target xs ∧ Frame target s.val t.val := by
  obtain ⟨so,hs⟩ := hs
  obtain ⟨origin,ht⟩ := ht
  obtain ⟨a,ea,ha,fa⟩ := WordCall.clear target input tape ys origin s ht
  obtain ⟨t,et,tt,tf⟩ := WordCall.clone source target hne input tape xs so (origin+ys.length) a
    (by simpa [ha,hne] using hs) (by simp [ha])
  refine ⟨t,?_,⟨origin+ys.length,by simp [tt]⟩,?_⟩
  · convert ea.seq et using 1 <;> first | rfl | omega
  · refine ⟨tf.1.trans fa.1,tf.2.1.trans fa.2.1,tf.2.2.1.trans fa.2.2.1,
      tf.2.2.2.1.trans fa.2.2.2.1,tf.2.2.2.2.1.trans fa.2.2.2.2.1,?_,?_⟩
    · intro i hi; simp [tt,ha,hi]
    · intro i h24 h25 h26 h27
      exact (tf.2.2.2.2.2.2 i h24 h25 h26 h27).trans (fa.2.2.2.2.2.2 i h26 h27)

end Maxwell.Cost.WordReplace
