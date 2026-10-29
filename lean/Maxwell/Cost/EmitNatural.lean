import Maxwell.Cost.EmitNat
import Maxwell.Cost.WordTransfer
import Maxwell.Cost.Structured.Primitive

namespace Maxwell.Cost.EmitNatural
open Structured

def code (workTape : ℕ) : Code :=
  .seq (.call (EmitNat.program workTape)) (.call (Rewind.program workTape))

def Frame (s t : Store) : Prop :=
  t.val.address = s.val.address ∧ t.val.inputHead = s.val.inputHead ∧
  t.val.memory = s.val.memory ∧ t.val.randomCursor = s.val.randomCursor ∧
  t.val.tapes = s.val.tapes

/-- Serialization scans the actual word, emits its length header and data,
and restores the source head for subsequent use. -/
theorem executes_with_registers (workTape n : ℕ) (origin : ℤ) (input : List Bool)
    (randomTape : ℕ → Bool) (s : Store)
    (hw : s.val.tapes workTape = BitTape.shifted n.bits origin) :
    ∃ t : Store, Executes input randomTape (code workTape) (20*n.bits.length+24) s t ∧
      t.val.output = (Codec.nat n).reverse ++ s.val.output ∧ Frame s t ∧
      (∀ i, i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 28 →
        t.val.registers i = s.val.registers i) := by
  have hp : (s.val.tapes workTape).Represents n.bits := by
    rw [hw]
    intro k
    simp [BitTape.shifted]
  have hz : (s.val.tapes workTape).cells ((s.val.tapes workTape).head-1) = none := by
    simp [hw, BitTape.shifted]
  have he := EmitNat.steps workTape input randomTape n.bits s.val s.property hp hz
  let e : Store := Store.ofState (EmitNat.finish workTape n.bits s.val)
  have hcall : Executes input randomTape (.call (EmitNat.program workTape))
      (16*n.bits.length+18) s e :=
    Executes.call _ _ _ _ he (by simp [EmitNat.program, EmitNat.finish, TapeIO.program, Rewind.program,
      BitRAMInstruction.relocate])
  have heword : e.val.tapes workTape = BitTape.shiftedEnd n.bits origin := by
    change (EmitNat.finish workTape n.bits s.val).tapes workTape = _
    rw [EmitNat.finish_tape, hw]
    rfl
  obtain ⟨hr, hrword⟩ := WordTransfer.rewind_shifted workTape origin input randomTape
    n.bits e.val e.property heword
  let t : Store := Store.ofState (Rewind.finishAt workTape origin e.val)
  have hrewind : Executes input randomTape (.call (Rewind.program workTape))
      (4*n.bits.length+6) e t :=
    Executes.call _ _ _ _ hr (by simp [Rewind.program, Rewind.finishAt])
  refine ⟨t, ?_, ?_, ?_, ?_⟩
  · convert hcall.seq hrewind using 1 <;> first | rfl | omega
  · exact EmitNat.finish_output workTape n.bits s.val
  · refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    funext i
    by_cases hi : i = workTape
    · subst i
      exact hrword.trans hw.symm
    · simp [t, e, Store.ofState, Rewind.finishAt, EmitNat.finish, EmitNat.payloadStart,
        EmitNat.rewindStart, EmitNat.separatorStart, EmitNat.headerStart, TapeIO.finish, hi]

  · intro i h24 h25 h26 h27 h28
    simp [t,e,Store.ofState,Rewind.finishAt,EmitNat.finish,EmitNat.payloadStart,
      EmitNat.rewindStart,EmitNat.separatorStart,EmitNat.headerStart,TapeIO.finish,
      h24,h25,h26,h27,h28]

theorem executes (workTape n : ℕ) (origin : ℤ) (input : List Bool)
    (randomTape : ℕ → Bool) (s : Store)
    (hw : s.val.tapes workTape = BitTape.shifted n.bits origin) :
    ∃ t : Store, Executes input randomTape (code workTape) (20*n.bits.length+24) s t ∧
      t.val.output = (Codec.nat n).reverse ++ s.val.output ∧ Frame s t := by
  obtain ⟨t,he,ho,hf,_⟩ := executes_with_registers workTape n origin input randomTape s hw
  exact ⟨t,he,ho,hf⟩

end Maxwell.Cost.EmitNatural
