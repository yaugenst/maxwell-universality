import Maxwell.Continuum.WellOriginalPassExecution
import Maxwell.Cost.Structured.WordLiteral

/-! Both original-pass cursors are reset by charged word replacement;
count setup, iteration, and cleanup then use the stored original count. -/
namespace Maxwell.Continuum.RationalDataflow.WellOriginalPass
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 3500000

def initializeCode : Code := .seq (WordLiteral.code 998 0) (WordLiteral.code 999 0)

theorem initialize_executes {n J i : ℕ} (p : Plan n J) (a : PartArray.Table J) (memory : ℕ→Bool)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (h : State p a i memory s) :
    ∃t,Executes input tape initializeCode (12*i.bits.length+22) s t ∧
      State p a 0 memory t ∧ BinaryPrecision.Frame {998,999} s.val t.val := by
  obtain ⟨u,e0,w0,f0⟩ := WordLiteral.executes 998 0 input tape i.bits s h.sourceIndex
  obtain ⟨t,e1,w1,f1⟩ := WordLiteral.executes 999 0 input tape i.bits u
    (word_of_eq (f0.tapes 999 (by decide)) h.outputIndex)
  have frame : BinaryPrecision.Frame {998,999} s.val t.val :=
    (f0.mono (by decide)).trans (f1.mono (by decide))
  refine ⟨t,?_,h.external_frame (frame.mono (by decide))
    (word_of_eq (f1.tapes 998 (by decide)) w0) w1,frame⟩
  convert e0.seq e1 using 1 <;> first | rfl | simp;omega

def fullCode : Code := .seq initializeCode runCode

theorem full_executes {n J i : ℕ} (p : Plan n J) (a : PartArray.Table J) (memory : ℕ→Bool)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (h : State p a i memory s)
    (old : List Bool) (hold : BankArray.Word s.val 972 old) :
    ∃cost t a',Executes input tape fullCode cost s t ∧
      cost ≤ 12*i.bits.length+6*old.length+21*n.bits.length+47+
        (n+1)*(13*n.bits.length+15)+n*stepCost p ∧
      State p a' n memory t ∧ a'.CorrectPrefix p.parts n ∧ Blank t.val 972 ∧
      (∀k,preserved k→t.val.tapes k=s.val.tapes k) := by
  obtain ⟨u,e0,h0,f0⟩ := initialize_executes p a memory input tape s h
  obtain ⟨cost,t,b,e1,hc,h1,completed,blank,keep⟩ := run_executes p a memory input tape u h0 old
    (BankArray.word_of_eq (f0.tapes 972 (by decide)) hold)
  refine ⟨_,t,b,e0.seq e1,by omega,h1,completed,blank,?_⟩
  intro k hk
  exact (keep k hk).trans (f0.tapes k (by
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
    exact ⟨hk.2.2.2.2.2.1,hk.2.2.2.2.2.2⟩))

#print axioms full_executes
end Maxwell.Continuum.RationalDataflow.WellOriginalPass
