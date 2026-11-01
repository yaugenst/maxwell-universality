import Maxwell.Cost.Structured.Footprint

/-! Literal program syntax certifies preservation of the immutable-input
head and random-seed cursor. Work-tape reads and moves remain unrestricted. -/
namespace Maxwell.Cost

def BitRAMInstruction.protectsInputPositions : BitRAMInstruction→Bool
  | .inputLeft | .inputRight | .randomBit _ => false
  | _ => true

def BitRAM.protectsInputPositions (body : BitRAM) : Bool :=
  body.code.all BitRAMInstruction.protectsInputPositions

theorem BitRAM.protectsInputPositions_next {body : BitRAM} (hp : body.protectsInputPositions=true)
    (input : List Bool) (tape : ℕ→Bool) (s t : BitRAMState) (extra : ℕ)
    (hn : body.next input tape s=some ⟨t,extra⟩) :
    (t.inputHead,t.randomCursor)=(s.inputHead,s.randomCursor) := by
  cases hi : body.code[s.pc]? with
  | none => simp [BitRAM.next,hi] at hn
  | some instruction =>
    have hs:=List.all_eq_true.mp hp instruction (List.mem_of_getElem? hi)
    cases instruction <;>
      simp only [BitRAM.next,hi,Option.some.injEq,PricedStep.mk.injEq,
        BitRAMInstruction.protectsInputPositions] at hn hs <;>
      first | contradiction | rcases hn with ⟨rfl,rfl⟩;rfl

theorem PricedSteps.protectsInputPositions {body : BitRAM} {cost : ℕ}
    {input : List Bool} {tape : ℕ→Bool} {s t : BitRAMState}
    (run : PricedSteps (body.next input tape) cost s t) (hp : body.protectsInputPositions=true) :
    (t.inputHead,t.randomCursor)=(s.inputHead,s.randomCursor) :=
  run.conserved (fun s=>(s.inputHead,s.randomCursor)) (body.protectsInputPositions_next hp input tape)

namespace Structured
def Code.protectsInputPositions : Code→Bool
  | .skip => true
  | .call body => body.protectsInputPositions
  | .seq first second => first.protectsInputPositions && second.protectsInputPositions
  | .branch _ yes no => yes.protectsInputPositions && no.protectsInputPositions
  | .loop _ body => body.protectsInputPositions

theorem Executes.protectsInputPositions {input : List Bool} {tape : ℕ→Bool} {code : Code}
    {cost : ℕ} {s t : Store} (run : Executes input tape code cost s t) (hp : code.protectsInputPositions=true) :
    t.val.inputHead=s.val.inputHead ∧t.val.randomCursor=s.val.randomCursor := by
  induction run with
  | skip => exact ⟨rfl,rfl⟩
  | call body s t cost steps _ => exact Prod.mk.inj (steps.protectsInputPositions hp)
  | seq _ _ ih1 ih2 =>
    simp only [Code.protectsInputPositions,Bool.and_eq_true] at hp
    exact ⟨(ih2 hp.2).1.trans (ih1 hp.1).1,(ih2 hp.2).2.trans (ih1 hp.1).2⟩
  | yes _ _ ih =>
    simp only [Code.protectsInputPositions,Bool.and_eq_true] at hp
    exact ih hp.1
  | no _ _ ih =>
    simp only [Code.protectsInputPositions,Bool.and_eq_true] at hp
    exact ih hp.2
  | done => exact ⟨rfl,rfl⟩
  | more _ _ _ ih1 ih2 => exact ⟨(ih2 hp).1.trans (ih1 hp).1,(ih2 hp).2.trans (ih1 hp).2⟩
end Structured
end Maxwell.Cost
