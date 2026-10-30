import Maxwell.Cost.Structured.Footprint

/-! Literal finite code without output instructions preserves the existing
serialized output. This applies to loops as well as arithmetic calls. -/
namespace Maxwell.Cost

def BitRAMInstruction.silent : BitRAMInstruction → Bool
  | .output _ => false
  | _ => true

def BitRAM.silent (body : BitRAM) : Bool := body.code.all BitRAMInstruction.silent

theorem BitRAM.silent_next {body : BitRAM} (hp : body.silent=true)
    (input : List Bool) (randomTape : ℕ→Bool) (s t : BitRAMState) (extra : ℕ)
    (hn : body.next input randomTape s=some ⟨t,extra⟩) : t.output=s.output := by
  cases hi : body.code[s.pc]? with
  | none => simp [BitRAM.next,hi] at hn
  | some instruction =>
    have hs := List.all_eq_true.mp hp instruction (List.mem_of_getElem? hi)
    cases instruction <;>
      simp only [BitRAM.next,hi,Option.some.injEq,PricedStep.mk.injEq,
        BitRAMInstruction.silent] at hn hs <;>
      first
      | contradiction
      | rcases hn with ⟨rfl,rfl⟩
        rfl

theorem PricedSteps.silent {body : BitRAM} {cost : ℕ} {input : List Bool}
    {randomTape : ℕ→Bool} {s t : BitRAMState}
    (run : PricedSteps (body.next input randomTape) cost s t)
    (hp : body.silent=true) : t.output=s.output :=
  run.conserved (fun s => s.output) (body.silent_next hp input randomTape)

namespace Structured

def Code.silent : Code → Bool
  | .skip => true
  | .call body => body.silent
  | .seq first second => first.silent && second.silent
  | .branch _ yes no => yes.silent && no.silent
  | .loop _ body => body.silent

theorem Executes.silent {input : List Bool} {randomTape : ℕ→Bool} {code : Code}
    {cost : ℕ} {s t : Store} (run : Executes input randomTape code cost s t)
    (hp : code.silent=true) : t.val.output=s.val.output := by
  induction run with
  | skip => rfl
  | call body s t cost steps _ => exact steps.silent hp
  | seq _ _ ih1 ih2 =>
    simp only [Code.silent,Bool.and_eq_true] at hp
    exact (ih2 hp.2).trans (ih1 hp.1)
  | yes _ _ ih =>
    simp only [Code.silent,Bool.and_eq_true] at hp
    exact ih hp.1
  | no _ _ ih =>
    simp only [Code.silent,Bool.and_eq_true] at hp
    exact ih hp.2
  | done => rfl
  | more _ _ _ ih1 ih2 => exact (ih2 hp).trans (ih1 hp)

end Structured
end Maxwell.Cost
