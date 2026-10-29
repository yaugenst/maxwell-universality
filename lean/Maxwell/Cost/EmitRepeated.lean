import Maxwell.Cost.EmitLiteral
import Maxwell.Cost.Structured.CountedShifted

namespace Maxwell.Cost.EmitRepeated
open Structured
open scoped BigOperators

def code (countTape : ℕ) (bits : List Bool) : Code :=
  Counted.code countTape (EmitLiteral.code 30 bits)

/-- A variable repetition count is consumed by actual binary decrements.
Only the repeated block is a compile-time constant. -/
theorem executes (countTape n : ℕ) (bits : List Bool) (origin : ℤ)
    (input : List Bool) (randomTape : ℕ → Bool) (s : Store)
    (hw : s.val.tapes countTape = BitTape.shifted n.bits origin) :
    ∃ cost, ∃ t : Store, Executes input randomTape (code countTape bits) cost s t ∧
      cost ≤ (n+1)*(13*n.bits.length+15)+n*(4*bits.length+1) ∧
      t.val.output = (List.replicate n bits).flatten.reverse ++ s.val.output ∧
      t.val.randomCursor = s.val.randomCursor := by
  let invariant (k : ℕ) (t : Store) : Prop := k ≤ n ∧
    t.val.output = (List.replicate (n-k) bits).flatten.reverse ++ s.val.output ∧
    t.val.randomCursor = s.val.randomCursor
  have stable : ∀ k a b, Counted.Frame countTape a b → invariant k a → invariant k b := by
    intro k a b hf hi
    exact ⟨hi.1, hf.2.2.2.2.1.trans hi.2.1, hf.2.2.2.1.trans hi.2.2⟩
  have body : ∀ k xs a, invariant (k+1) a →
      a.val.tapes countTape = BitTape.shifted xs origin → addressValue xs = k →
      ∃ c b, Executes input randomTape (EmitLiteral.code 30 bits) c a b ∧
        invariant k b ∧ b.val.tapes countTape = BitTape.shifted xs origin ∧
        c ≤ 4*bits.length+1 := by
    intro k xs a hi hx _
    let b := EmitLiteral.finish 30 bits a
    have hf := EmitLiteral.finish_frame 30 bits a
    refine ⟨_, b, EmitLiteral.executes 30 bits input randomTape a, ⟨by omega, ?_,
      hf.2.2.2.1.trans hi.2.2⟩, ?_, le_rfl⟩
    · rw [EmitLiteral.finish_output, hi.2.1]
      have hd : n-k = (n-(k+1))+1 := by omega
      rw [hd, List.replicate_add, List.flatten_append, List.reverse_append]
      simp [List.append_assoc]
    · exact (congrFun hf.2.2.2.2.1 countTape).trans hx
  obtain ⟨cost, t, final, he, hi, _, _, _, hc⟩ := CountedShifted.executes
    countTape origin (EmitLiteral.code 30 bits) input randomTape invariant
    (fun _ => 4*bits.length+1) stable body n n.bits s (addressValue_bits n) hw
    ⟨le_rfl, by simp, rfl⟩
  refine ⟨cost, t, he, ?_, ?_, hi.2.2⟩
  · simpa using hc
  · simpa using hi.2.1

end Maxwell.Cost.EmitRepeated
