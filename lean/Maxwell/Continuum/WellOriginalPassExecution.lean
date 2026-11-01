import Maxwell.Continuum.WellOriginalPassLoop
import Maxwell.Cost.Structured.CounterClear

/-! The original-strength pass copies its runtime count from tape 963,
executes the chronological loop, and clears the padded countdown word. -/
namespace Maxwell.Continuum.RationalDataflow.WellOriginalPass
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def runCode : Code := .seq (WordReplace.code 963 972)
  (.seq code (.call (TapeOps.clear 972)))

theorem run_executes {n J : ℕ} (p : Plan n J) (a : PartArray.Table J) (memory : ℕ→Bool)
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (h : State p a 0 memory s)
    (old : List Bool) (hold : BankArray.Word s.val 972 old) :
    ∃cost t a',Executes input tape runCode cost s t ∧
      cost ≤ 6*old.length+21*n.bits.length+25+
        (n+1)*(13*n.bits.length+15)+n*stepCost p ∧
      State p a' n memory t ∧ a'.CorrectPrefix p.parts n ∧ Blank t.val 972 ∧
      (∀k,preserved k→t.val.tapes k=s.val.tapes k) := by
  obtain ⟨u,e0,w0,f0⟩ := WordReplace.executes 963 972 (by decide) input tape n.bits old s h.originalCount hold
  have frame0 : BinaryPrecision.Frame external s.val u.val :=
    ⟨f0.1,f0.2.1,f0.2.2.1,f0.2.2.2.1,f0.2.2.2.2.1,fun k hk=>f0.2.2.2.2.2.1 k (by
      simp only [external,Finset.mem_insert,Finset.mem_singleton,not_or] at hk;omega)⟩
  have state0 := h.external_frame frame0
    (word_of_eq (f0.2.2.2.2.2.1 998 (by decide)) h.sourceIndex)
    (word_of_eq (f0.2.2.2.2.2.1 999 (by decide)) h.outputIndex)
  obtain ⟨origin,word⟩ := w0
  obtain ⟨c1,v,b,finalWord,e1,hc1,state1,completed,word1,len,_,keep1⟩ :=
    executes p a memory input tape u state0 n.bits origin (addressValue_bits n) word
  obtain ⟨t,e2,blank2,frame2⟩ := RuntimeCounter.clear_executes 972 input tape finalWord origin v word1
  have state2 := state1.external_frame (frame2.mono (by decide : ({972}:Finset ℕ)⊆external))
    (word_of_eq (frame2.tapes 998 (by decide)) state1.sourceIndex)
    (word_of_eq (frame2.tapes 999 (by decide)) state1.outputIndex)
  refine ⟨_,t,b,e0.seq (e1.seq e2),by rw [len];omega,state2,completed,blank2,?_⟩
  intro k hk
  exact (frame2.tapes k (by simpa only [Finset.mem_singleton] using hk.2.2.1)).trans
    ((keep1 k hk).trans (f0.2.2.2.2.2.1 k hk.2.2.1))

#print axioms run_executes
end Maxwell.Continuum.RationalDataflow.WellOriginalPass
