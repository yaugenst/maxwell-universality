import Maxwell.Cost.SourceCircuit.EmitGate
import Maxwell.Cost.SourceCircuit.BankReplace

namespace Maxwell.Cost.SourceCircuit
open Structured
open RationalAccumulator (Blank)

def accumulatorWork : Finset ℕ := {94,95,96,97}

def emitAccumulatorCode (tag : List Bool) (parents : List ℕ) : Code :=
  .seq (emitGateCode tag parents) (replaceCode 96 94)

theorem emitAccumulator_executes (input : List Bool) (tape : ℕ → Bool)
    (tag next old preceding : List Bool) (parents : List (ℕ × List Bool)) (s : Store)
    (hscratch : BankArray.Scratch s.val) (h96 : Blank s.val 96)
    (hnext : BankArray.Word s.val 95 next) (hold : BankArray.Word s.val 94 old)
    (hparents : ∀ field ∈ parents, field.1 ≠ 96 ∧ field.1 ≠ 97 ∧ BankArray.Word s.val field.1 field.2)
    (h97 : s.val.tapes 97 = BitTape.atEnd preceding) :
    ∃ cost, ∃ t : Store,
      cost ≤ 39*next.length+6*old.length+6*tag.length+fieldCost parents+51 ∧
      Executes input tape (emitAccumulatorCode tag (parents.map Prod.fst)) cost s t ∧
      BankArray.Word t.val 95 (Increment.bits next) ∧ BankArray.Word t.val 94 next ∧
      Blank t.val 96 ∧
      t.val.tapes 97 = BitTape.atEnd (preceding ++ tag ++ parents.flatMap Prod.snd) ∧
      t.val.memory = s.val.memory ∧ BankArray.Scratch t.val ∧ Frame accumulatorWork s.val t.val := by
  obtain ⟨ec,e,hec,ee,en,eo,eg,em,es,ef⟩ := emitGate_executes input tape tag next preceding
    parents s hscratch h96 hnext hparents h97
  obtain ⟨t,et,ta,t96,tm,tf,tk⟩ := replace_executes 96 94 (by omega) input tape next old e eo
    (BankArray.word_of_eq (ef.tapes 94 (by omega) (by simp [gateWork])) hold)
  refine ⟨_,t,?_,ee.seq et,BankArray.word_of_eq (tk 95 (by omega) (by omega)) en,ta,t96,
    (tk 97 (by omega) (by omega)).trans eg,tm.trans em,
    scratch_of_tapes es (fun j hj => tk j (by omega) (by omega)),
    (ef.mono (by simp [gateWork,accumulatorWork])).trans
      (tf.mono (by
        intro j hj
        simp only [Finset.mem_insert,Finset.mem_singleton] at hj
        rcases hj with rfl | rfl <;> simp [accumulatorWork]))⟩
  omega

end Maxwell.Cost.SourceCircuit
