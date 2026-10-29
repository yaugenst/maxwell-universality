import Maxwell.Cost.EmitNat
import Maxwell.Cost.RationalAccumulator.Bank

namespace Maxwell.Cost.DecoderParser.Output
open Structured

/-- Emit the vector length and restore its retained metadata word. -/
def headerCode : Code := .seq (.call (EmitNat.program 40)) (.call (Rewind.program 40))

def Frame (s t : BitRAMState) : Prop :=
  t.address = s.address ∧ t.inputHead = s.inputHead ∧ t.memory = s.memory ∧
  t.randomCursor = s.randomCursor ∧ t.tapes = s.tapes ∧
  (∀ i, i ≠ 24 → i ≠ 25 → i ≠ 26 → i ≠ 27 → i ≠ 28 → t.registers i = s.registers i)

theorem header (input : List Bool) (randomTape : ℕ → Bool) (n : ℕ) (s : Store)
    (hw : RationalAccumulator.Word s.val 40 n) :
    ∃ t : Store, Executes input randomTape headerCode (20*n.bits.length+24) s t ∧
      t.val.output = (Codec.nat n).reverse ++ s.val.output ∧ Frame s.val t.val := by
  obtain ⟨origin,ho⟩ := hw
  have he := EmitNat.steps 40 input randomTape n.bits s.val s.property
    (by rw [ho]; intro k; simp [BitTape.shifted])
    (by simp [ho,BitTape.shifted])
  let e := EmitNat.finish 40 n.bits s.val
  let eS := Store.ofState e
  have ee : Executes input randomTape (.call (EmitNat.program 40)) (16*n.bits.length+18) s eS :=
    .call _ _ _ _ he rfl
  have het : eS.val.tapes 40 = BitTape.shiftedEnd n.bits origin := by
    simpa [eS,Store.ofState,e,ho,BitTape.shiftedEnd,BitTape.shifted] using EmitNat.finish_tape 40 n.bits s.val
  have hr := WordTransfer.rewind_shifted 40 origin input randomTape n.bits eS.val eS.property het
  let r := Rewind.finishAt 40 origin eS.val
  let rS := Store.ofState r
  have er : Executes input randomTape (.call (Rewind.program 40)) (4*n.bits.length+6) eS rS :=
    .call _ _ _ _ hr.1 rfl
  refine ⟨rS,?_,?_,?_⟩
  · simpa only [headerCode,show 16*n.bits.length+18+(4*n.bits.length+6)=20*n.bits.length+24 by omega]
      using ee.seq er
  · exact EmitNat.finish_output 40 n.bits s.val
  · refine ⟨rfl,rfl,rfl,rfl,?_,?_⟩
    · funext i
      by_cases hi : i = 40
      · subst i; exact hr.2.trans ho.symm
      · simp [rS,Store.ofState,r,Rewind.finishAt,eS,e,EmitNat.finish,EmitNat.payloadStart,
          EmitNat.rewindStart,EmitNat.separatorStart,EmitNat.headerStart,TapeIO.finish,hi]
    · intro i h24 h25 h26 h27 h28
      simp [rS,Store.ofState,r,Rewind.finishAt,eS,e,EmitNat.finish,EmitNat.payloadStart,
        EmitNat.rewindStart,EmitNat.separatorStart,EmitNat.headerStart,TapeIO.finish,h24,h25,h26,h27,h28]

theorem header_run (input : List Bool) (randomTape : ℕ → Bool) (n : ℕ) (s : Store)
    (hw : RationalAccumulator.Word s.val 40 n) :
    ∃ t : Store,
      (runPriced (headerCode.compile.next input randomTape) (20*n.bits.length+25) s.val).finished =
        some (t.place headerCode.size) ∧
      (runPriced (headerCode.compile.next input randomTape) (20*n.bits.length+25) s.val).instructions =
        20*n.bits.length+24 ∧
      t.val.output = (Codec.nat n).reverse ++ s.val.output ∧ Frame s.val t.val := by
  obtain ⟨t,he,ho,hf⟩ := header input randomTape n s hw
  have hr := he.compiled_run (20*n.bits.length+25) (by omega)
  exact ⟨t,hr.1,hr.2,ho,hf⟩

end Maxwell.Cost.DecoderParser.Output
