import Maxwell.Cost.BankArray.Common

/-! Swap two persistent binary words using three actual move programs and
one blank temporary tape. There is no descriptor relabelling by the host. -/
namespace Maxwell.Cost.WordSwap
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)

def code (left right temp : ℕ) : Code :=
  .seq (.call (WordTransfer.move left temp))
    (.seq (.call (WordTransfer.move right left)) (.call (WordTransfer.move temp right)))

def Frame (left right temp : ℕ) (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.output = s.output ∧
  (∀ i, i ≠ left → i ≠ right → i ≠ temp → t.tapes i = s.tapes i) ∧
  (∀ i, i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → t.registers i = s.registers i)

private theorem move (source target : ℕ) (hne : source ≠ target)
    (input : List Bool) (tape : ℕ → Bool) (xs : List Bool)
    (s : Store) (hsource : Word s.val source xs) (htarget : Blank s.val target) :
    ∃ t, Executes input tape (.call (WordTransfer.move source target)) (12 * xs.length + 11) s t ∧
      Word t.val target xs ∧ Blank t.val source ∧ WordTransfer.Frame source target s.val t.val := by
  obtain ⟨so, hs⟩ := hsource
  obtain ⟨targetOrigin, ht⟩ := htarget
  obtain ⟨t, he, hp, hs', ht', hf⟩ := WordTransfer.move_steps source target hne input tape xs
    so targetOrigin s.val s.property hs ht
  refine ⟨Store.ofState t, .call _ s t _ he ?_, ⟨targetOrigin, ht'⟩, ⟨so + xs.length, hs'⟩, hf⟩
  simp [WordTransfer.move, hp, TapeOps.copyClear, Rewind.program, BitRAMInstruction.relocate]

/-- Exact charged swap, preserving all state outside the three tape heads
and the four ordinary word-operation registers. -/
theorem executes (left right temp : ℕ)
    (hLR : left ≠ right) (hLT : left ≠ temp) (hRT : right ≠ temp)
    (input : List Bool) (tape : ℕ → Bool) (xs ys : List Bool)
    (s : Store) (hleft : Word s.val left xs) (hright : Word s.val right ys) (htemp : Blank s.val temp) :
    ∃ t, Executes input tape (code left right temp) (12 * (2 * xs.length + ys.length) + 33) s t ∧
      Word t.val left ys ∧ Word t.val right xs ∧ Blank t.val temp ∧ Frame left right temp s.val t.val := by
  obtain ⟨a, ea, hat, hal, fa⟩ := move left temp hLT input tape xs s hleft htemp
  obtain ⟨b, eb, hbl, hbr, fb⟩ := move right left hLR.symm input tape ys a
    (BankArray.word_of_eq (fa.2.2.2.2.2.1 right hLR.symm hRT) hright) hal
  obtain ⟨t, et, htr, htt, ft⟩ := move temp right hRT.symm input tape xs b
    (BankArray.word_of_eq (fb.2.2.2.2.2.1 temp hRT.symm hLT.symm) hat) hbr
  refine ⟨t, ?_, BankArray.word_of_eq (ft.2.2.2.2.2.1 left hLT hLR) hbl, htr, htt, ?_⟩
  · convert ea.seq (eb.seq et) using 1 <;> first | rfl | omega
  · rcases fa with ⟨aa, ai, am, ar, ao, atapes, aregs⟩
    rcases fb with ⟨ba, bi, bm, br, bo, btapes, bregs⟩
    rcases ft with ⟨ta, ti, tm, tr, tout, ttapes, tregs⟩
    exact ⟨ta.trans (ba.trans aa), ti.trans (bi.trans ai), tm.trans (bm.trans am),
      tr.trans (br.trans ar), tout.trans (bo.trans ao),
      fun i hleft hright htemp => (ttapes i htemp hright).trans
        ((btapes i hright hleft).trans (atapes i hleft htemp)),
      fun i h24 h25 h26 h27 => (tregs i h24 h25 h26 h27).trans
        ((bregs i h24 h25 h26 h27).trans (aregs i h24 h25 h26 h27))⟩

end Maxwell.Cost.WordSwap
