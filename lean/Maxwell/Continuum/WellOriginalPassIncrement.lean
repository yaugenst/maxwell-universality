import Maxwell.Continuum.WellOriginalPassData

/-! Both chronological indices advance through executed canonical binary
increments. The countdown word and saved source memory are preserved. -/
namespace Maxwell.Continuum.RationalDataflow.WellOriginalPass
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.RationalAccumulator
set_option maxHeartbeats 2500000

def incrementCode : Code := .seq (PhysicalEmit.incrementCode 998) (PhysicalEmit.incrementCode 999)

theorem increment_executes {n J i : ℕ} {p : Plan n J} {a : PartArray.Table J} {memory : ℕ→Bool}
    (input : List Bool) (tape : ℕ→Bool) (s : Store) (h : State p a i memory s) :
    ∃cost t,Executes input tape incrementCode cost s t ∧ cost ≤ 24*i.bits.length+36 ∧
      State p a (i+1) memory t ∧ BinaryPrecision.Frame {998,999} s.val t.val := by
  obtain ⟨c0,u,hc0,e0,w0,f0⟩ := PhysicalEmit.increment 998 i input tape s h.sourceIndex
  have output0 : Word u.val 999 i := word_of_eq (f0.tapes 999 (by decide)) h.outputIndex
  obtain ⟨c1,t,hc1,e1,w1,f1⟩ := PhysicalEmit.increment 999 i input tape u output0
  have f := f0.trans f1
  have frame : BinaryPrecision.Frame {998,999} s.val t.val :=
    ⟨f.address,f.inputHead,f.memory,f.randomCursor,f.output,fun k hk=>f.tapes k (by simpa using hk)⟩
  have source1 : Word t.val 998 (i+1) := word_of_eq (f1.tapes 998 (by decide)) w0
  exact ⟨c0+c1,t,e0.seq e1,by omega,h.external_frame (frame.mono (by decide)) source1 w1,frame⟩

#print axioms increment_executes
end Maxwell.Continuum.RationalDataflow.WellOriginalPass
