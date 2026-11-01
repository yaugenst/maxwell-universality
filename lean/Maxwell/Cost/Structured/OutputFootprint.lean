import Maxwell.Cost.Structured.Syntax

/-! A syntactic output footprint lets a computed-table stage preserve an
already emitted description prefix on its actual Boolean execution. -/
namespace Maxwell.Cost

def BitRAMInstruction.protectsOutput : BitRAMInstruction→Bool
  | .output _ => false
  | _ => true

def BitRAM.protectsOutput (body : BitRAM) : Bool := body.code.all BitRAMInstruction.protectsOutput

theorem BitRAM.protectsOutput_next {body : BitRAM} (hp : body.protectsOutput=true)
    (input : List Bool) (randomTape : ℕ→Bool) (s t : BitRAMState) (extra : ℕ)
    (hn : body.next input randomTape s=some ⟨t,extra⟩) : t.output=s.output := by
  cases hi : body.code[s.pc]? with
  | none => simp [BitRAM.next,hi] at hn
  | some instruction =>
    have hs := List.all_eq_true.mp hp instruction (List.mem_of_getElem? hi)
    cases instruction <;>
      simp only [BitRAM.next,hi,Option.some.injEq,PricedStep.mk.injEq,BitRAMInstruction.protectsOutput] at hn hs <;>
      first
      | contradiction
      | rcases hn with ⟨rfl,rfl⟩
        simp_all [BitRAMState.setTape,BitRAMState.setRegister]

theorem PricedSteps.protectsOutput {body : BitRAM} {cost : ℕ} {input : List Bool}
    {randomTape : ℕ→Bool} {s t : BitRAMState}
    (run : PricedSteps (body.next input randomTape) cost s t) (hp : body.protectsOutput=true) :
    t.output=s.output := run.conserved (fun s=>s.output) (body.protectsOutput_next hp input randomTape)

namespace Structured

def Code.protectsOutput : Code→Bool
  | .skip => true
  | .call body => body.protectsOutput
  | .seq first second => first.protectsOutput && second.protectsOutput
  | .branch _ yes no => yes.protectsOutput && no.protectsOutput
  | .loop _ body => body.protectsOutput

theorem Executes.protectsOutput {input : List Bool} {randomTape : ℕ→Bool}
    {code : Code} {cost : ℕ} {s t : Store} (run : Executes input randomTape code cost s t)
    (hp : code.protectsOutput=true) : t.val.output=s.val.output := by
  induction run with
  | skip => rfl
  | call body s t cost steps _ => exact steps.protectsOutput hp
  | seq _ _ ih1 ih2 =>
    simp only [Code.protectsOutput,Bool.and_eq_true] at hp
    exact (ih2 hp.2).trans (ih1 hp.1)
  | yes _ _ ih =>
    simp only [Code.protectsOutput,Bool.and_eq_true] at hp
    exact ih hp.1
  | no _ _ ih =>
    simp only [Code.protectsOutput,Bool.and_eq_true] at hp
    exact ih hp.2
  | done => rfl
  | more _ _ _ ih1 ih2 => exact (ih2 hp).trans (ih1 hp)

#print axioms Executes.protectsOutput
end Structured
end Maxwell.Cost
