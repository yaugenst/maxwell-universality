import Maxwell.Cost.DecoderParser.Schema

/-! A charged schema traversal that leaves no archive or parser workspace.
It can precede a separately encoded payload without changing its machine state. -/

namespace Maxwell.Cost.DecoderParser
open Structured

def skip (shape : Shape) : Code :=
  .seq (parser shape 0) (.call (TapeReset.program 18))

def skipPrice (shape : Shape) (x : Payload shape) : ℕ :=
  price shape x + 6*(wire shape x).length+6

theorem skip_correct (shape : Shape) (hheight : shape.height≤14)
    (x : Payload shape) (preceding suffix : List Bool) (randomTape : ℕ→Bool)
    (s : Store) (hh : s.val.inputHead=preceding.length) (hr : Ready 0 s.val)
    (ha : s.val.tapes 18=BitTape.blank) :
    ∃ cost t, Executes (preceding++(wire shape x++suffix)) randomTape (skip shape) cost s t ∧
      cost≤skipPrice shape x ∧ t.val.inputHead=(preceding++wire shape x).length ∧
      Frame ∅ s.val t.val := by
  obtain ⟨cost,u,eu,hcost,huh,hu18,huf⟩ :=
    parser_correct shape 0 (by simpa using hheight) x preceding suffix [] randomTape s hh hr
      (by simpa [BitTape.atEnd_nil] using ha)
  simp only [List.nil_append] at hu18
  let t := Store.ofState (TapeReset.finish 18 u.val)
  have et : Executes (preceding++(wire shape x++suffix)) randomTape
      (.call (TapeReset.program 18)) (6*(wire shape x).length+6) u t := by
    convert Executes.call (TapeReset.program 18) u (TapeReset.finish 18 u.val) _
      (TapeReset.steps 18 _ randomTape (wire shape x) u.val u.property hu18)
      (by simp [TapeReset.finish,TapeReset.program]) using 1
  refine ⟨_,t,eu.seq et,by dsimp [skipPrice];omega,?_,?_⟩
  · change u.val.inputHead=_
    simpa [hh] using huh
  · refine ⟨huf.address,huf.memory,huf.randomCursor,huf.output,?_⟩
    intro i _
    by_cases hi : i=18
    · subst i
      exact (TapeReset.finish_tape 18 u.val).trans ha.symm
    · change (TapeReset.finish 18 u.val).tapes i=_
      simpa [TapeReset.finish,hi] using huf.tapes i (by simpa using hi)

#print axioms skip_correct

end Maxwell.Cost.DecoderParser
