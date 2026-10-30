import Maxwell.Cost.EmitNatural

/-! Literal output of an already stored Boolean payload, followed by a
charged rewind. The word is runtime data, never compiled into instructions. -/
namespace Maxwell.Continuum.StoredBitPayload
open Maxwell.Cost Maxwell.Cost.Structured
set_option maxHeartbeats 2200000
set_option maxRecDepth 8192

def code (workTape : ℕ) : Code :=
  .seq (.call (TapeIO.program workTape false)) (.call (Rewind.program workTape))

theorem executes (workTape : ℕ) (bits : List Bool) (origin : ℤ)
    (input : List Bool) (tape : ℕ→Bool) (s : Store)
    (hw : s.val.tapes workTape=BitTape.shifted bits origin) :
    ∃t,Executes input tape (code workTape) (10*bits.length+10) s t ∧
      t.val.output=bits.reverse++s.val.output ∧ EmitNatural.Frame s t := by
  have hp : (s.val.tapes workTape).Represents bits := by
    rw [hw]
    intro k
    simp [BitTape.shifted]
  have he := TapeIO.steps workTape false input tape bits s.val s.property hp (by simp)
  let e : Store := Store.ofState (TapeIO.finish workTape false bits s.val)
  have call : Executes input tape (.call (TapeIO.program workTape false)) (6*bits.length+4) s e :=
    Executes.call _ _ _ _ he (by simp [TapeIO.program,TapeIO.finish])
  have endWord : e.val.tapes workTape=BitTape.shiftedEnd bits origin := by
    change (TapeIO.finish workTape false bits s.val).tapes workTape=_
    simp only [TapeIO.finish,Function.update_self,hw]
    rfl
  obtain ⟨hr,hrword⟩ := WordTransfer.rewind_shifted workTape origin input tape bits e.val e.property endWord
  let t : Store := Store.ofState (Rewind.finishAt workTape origin e.val)
  have rewind : Executes input tape (.call (Rewind.program workTape)) (4*bits.length+6) e t :=
    Executes.call _ _ _ _ hr (by simp [Rewind.program,Rewind.finishAt])
  refine ⟨t,?_,?_,⟨rfl,rfl,rfl,rfl,?_⟩⟩
  · convert call.seq rewind using 1 <;> first | rfl | omega
  · have hid : TapeIO.symbol false=(fun b:Bool=>b) := rfl
    simp [t,e,Store.ofState,Rewind.finishAt,TapeIO.finish,hid]
  · funext i
    by_cases hi : i=workTape
    · subst i;exact hrword.trans hw.symm
    · simp [t,e,Store.ofState,Rewind.finishAt,TapeIO.finish,hi]

#print axioms executes
end Maxwell.Continuum.StoredBitPayload
