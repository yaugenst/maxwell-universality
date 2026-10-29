import Maxwell.Cost.RealPrivate.Frame

namespace Maxwell.Cost.RealPrivate
open RealSimulation.Control

/-- Appending a logical address changes only the chronological write log
and its cursor. Both simulated memory banks and accumulated outputs survive. -/
theorem Represents.logged {origin : ℕ} {source : RAMState} {written : List ℕ}
    {s : Store} (h : Represents origin source written s.val) :
    Represents origin source (s.val.indices coordinateRegister :: written) (logged s).val := by
  have hlogged : RealPrivate.logged s =
      ((s.put pointerRegister (slot origin 2 written.length)).put
        (slot origin 2 written.length) (s.val.indices coordinateRegister)).put
        logLength (written.length+1) := by
    simp only [RealPrivate.logged,h.origin_word,h.log_length]
  rw [hlogged]
  have hn (j : ℕ) (hj : j < 256) : j ≠ slot origin 2 written.length :=
    (slot_ne_small h.high 2 written.length j hj).symm
  have hz (a : ℕ) : slot origin 0 a ≠ slot origin 2 written.length :=
    slot_different (by decide) (by decide) (by decide)
  have ho (a : ℕ) : slot origin 1 a ≠ slot origin 2 written.length :=
    slot_different (by decide) (by decide) (by decide)
  have hl (bank a : ℕ) (j : ℕ) (hj : j < 256) : slot origin bank a ≠ j :=
    slot_ne_small h.high bank a j hj
  refine ⟨h.high,?_,?_,?_,?_,h.words,?_,?_,?_,h.real_output,?_,?_,?_,h.random_cursor⟩
  · simpa [hn,originRegister,pointerRegister,logLength] using h.origin_word
  · simpa [hn,zeroRegister,pointerRegister,logLength] using h.zero
  · simpa [hn,oneRegister,pointerRegister,logLength] using h.one
  · simpa [hn,sourcePC,pointerRegister,logLength] using h.pc
  · intro a
    simpa [hz,hl,pointerRegister,logLength] using h.indices a
  · simpa [hn,realOutputLength,pointerRegister,logLength] using h.real_output_length
  · simpa [hn,indexOutputLength,pointerRegister,logLength] using h.index_output_length
  · intro j hj
    simpa [ho,hl,pointerRegister,logLength] using h.index_output j hj
  · simp [logLength]
  · intro j hj
    simp only [List.length_cons] at hj
    by_cases he : j=written.length
    · subst j
      simp [hl,pointerRegister,logLength,List.reverse_cons]
    · have hj' : j < written.length := by omega
      have hneq : slot origin 2 j ≠ slot origin 2 written.length := by simpa using he
      simpa [hl,hneq,pointerRegister,logLength,
        List.reverse_cons,List.getElem?_append_left (show j<written.reverse.length by simpa using hj')]
        using h.log_cells j hj'

end Maxwell.Cost.RealPrivate
