import Maxwell.Cost.ChildPermutation.Common
import Maxwell.Cost.PowerOfTwo

namespace Maxwell.Cost.ChildPermutation
open Structured
open BankArray (Word)
open RationalAccumulator (Blank)

def countCode : Code := .seq (.call (WordTransfer.clone 96 127))
  (.seq (.atom (.eraseTape 127)) (.atom (.tapeRight 127)))

/-- A power-of-two parent count loses its low zero bit to become the exact
child count, with its left sentinel physically cleared. -/
theorem count_executes (k : ℕ) (input : List Bool) (tape : ℕ → Bool) (s : Store)
    (h96 : Word s.val 96 (2*(2^k)).bits) (h127 : Blank s.val 127) :
    ∃ t, Executes input tape countCode (15*(2*(2^k)).bits.length+21) s t ∧
      Word t.val 127 (2^k).bits ∧ t.val.memory=s.val.memory ∧
      (∀ i, i≠127 → t.val.tapes i=s.val.tapes i) ∧ WordTransfer.Frame 96 127 s.val t.val := by
  obtain ⟨so,hso⟩ := h96
  obtain ⟨origin,ho⟩ := h127
  obtain ⟨a,ea,atapes,af⟩ := WordCall.clone 96 127 (by omega) input tape (2*(2^k)).bits so origin s hso ho
  let b : Store := Store.ofState (a.val.setTape 127 ((a.val.tapes 127).write none))
  let t : Store := Store.ofState (b.val.setTape 127 {b.val.tapes 127 with head:=(b.val.tapes 127).head+1})
  have eb : Executes input tape (.atom (.eraseTape 127)) 2 a b := Executes.eraseTape input tape a 127
  have et : Executes input tape (.atom (.tapeRight 127)) 2 b t := Executes.tapeRight input tape b 127
  have hbits : (2*(2^k)).bits=false::(2^k).bits := by
    rw [← pow_succ']
    simp [PowerOfTwo.power_bits,List.replicate_succ]
  have target : t.val.tapes 127=BitTape.shifted (2^k).bits (origin+1) := by
    simp only [t,b,Store.ofState,BitRAMState.setTape,Function.update_self,atapes,hbits]
    exact BitTape.shifted_erase_move false (2^k).bits origin
  have keep (i : ℕ) (hi : i≠127) : t.val.tapes i=s.val.tapes i := by
    simp [t,b,Store.ofState,BitRAMState.setTape,hi,atapes]
  refine ⟨t,?_,⟨origin+1,target⟩,af.2.2.1,keep,?_⟩
  · exact ea.seq (eb.seq et)
  · exact ⟨af.1,af.2.1,af.2.2.1,af.2.2.2.1,af.2.2.2.2.1,
      fun i _ hi => keep i hi,af.2.2.2.2.2.2⟩

end Maxwell.Cost.ChildPermutation
