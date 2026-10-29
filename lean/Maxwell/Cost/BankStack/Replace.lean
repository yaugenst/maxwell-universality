import Maxwell.Cost.BankStack.Pop

namespace Maxwell.Cost.BankStack
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)

def replaceCode (stack clock target : ℕ) : Code :=
  .seq (.call (TapeOps.clear target)) (popCode stack clock target)

theorem replace (stack clockBank target : ℕ)
    (ha : 10 ≤ stack) (ht : 10 ≤ target)
    (hac : stack≠clockBank) (hat : stack≠target) (hct : clockBank≠target)
    (input : List Bool) (tape : ℕ → Bool) (value : ℕ) (old clock preceding : List Bool)
    (hfit : value.bits.length≤clock.length) (hold : old.length≤clock.length)
    (s : Store) (hstack : s.val.tapes stack=BitTape.atEnd (preceding++FixedWidth.bits clock.length value.bits))
    (htarget : Word s.val target old) (hclockBank : Word s.val clockBank clock)
    (scratch : BankArray.Scratch s.val) (h7 : Blank s.val 7) :
    ∃ cost t, cost≤37*clock.length+32 ∧ Executes input tape (replaceCode stack clockBank target) cost s t ∧
      t.val.tapes stack=BitTape.atEnd preceding ∧ Word t.val target value.bits ∧
      t.val.tapes clockBank=s.val.tapes clockBank ∧ BankArray.Scratch t.val ∧ Blank t.val 7 ∧
      t.val.memory=s.val.memory ∧ SourceCircuit.Frame {stack,target} s.val t.val := by
  obtain ⟨origin,htarget⟩ := htarget
  obtain ⟨p,ep,ptapes,pframe⟩ := WordCall.clear target input tape old origin s htarget
  have pk (i : ℕ) (hi : i≠target) : p.val.tapes i=s.val.tapes i := by simp [ptapes,hi]
  obtain ⟨cost,t,hcost,et,tstack,ttarget,tclock,ts,t7,tm,tframe⟩ := pop_canonical stack clockBank target
    ha ht hac hat hct input tape value clock preceding hfit p ((pk stack hat).trans hstack)
    ⟨origin+old.length,by simp [ptapes]⟩
    (BankArray.word_of_eq (pk clockBank hct) hclockBank)
    (SourceCircuit.scratch_of_tapes scratch (fun i hi => pk i (by omega)))
    (RationalAccumulator.blank_of_eq (pk 7 (by omega)) h7)
  have pf : SourceCircuit.Frame {stack,target} s.val p.val :=
    SourceCircuit.frame_transfer (WordTransfer.frame_of_copy pframe)
      (fun i hi => pk i (by simp_all))
  exact ⟨6*old.length+4+cost,t,by omega,ep.seq et,tstack,ttarget,
    tclock.trans (pk clockBank hct),ts,t7,tm.trans pframe.2.2.1,pf.trans tframe⟩

end Maxwell.Cost.BankStack
