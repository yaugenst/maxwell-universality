import Maxwell.Cost.Structured.Footprint

/-! A finite program footprint certifies that executions preserve shared memory. -/
namespace Maxwell.Cost

def BitRAMInstruction.protectsMemory : BitRAMInstruction→Bool
  | .writeMemory _ => false
  | _ => true

def BitRAM.protectsMemory (body : BitRAM) : Bool := body.code.all BitRAMInstruction.protectsMemory

theorem BitRAM.protectsMemory_next {body : BitRAM} (hp : body.protectsMemory=true)
    (input : List Bool) (tape : ℕ→Bool) (s t : BitRAMState) (extra : ℕ)
    (hn : body.next input tape s=some ⟨t,extra⟩) : t.memory=s.memory := by
  cases hi : body.code[s.pc]? with
  | none => simp [BitRAM.next,hi] at hn
  | some instruction =>
    have hs := List.all_eq_true.mp hp instruction (List.mem_of_getElem? hi)
    cases instruction <;>
      simp only [BitRAM.next,hi,Option.some.injEq,PricedStep.mk.injEq,
        BitRAMInstruction.protectsMemory] at hn hs <;>
      first
      | contradiction
      | rcases hn with ⟨rfl,rfl⟩; rfl

theorem PricedSteps.protectsMemory {body : BitRAM} {cost : ℕ}
    {input : List Bool} {tape : ℕ→Bool} {s t : BitRAMState}
    (run : PricedSteps (body.next input tape) cost s t) (hp : body.protectsMemory=true) :
    t.memory=s.memory :=
  run.conserved (fun s => s.memory) (body.protectsMemory_next hp input tape)

namespace Structured
def Code.protectsMemory : Code→Bool
  | .skip => true
  | .call body => body.protectsMemory
  | .seq first second => first.protectsMemory && second.protectsMemory
  | .branch _ yes no => yes.protectsMemory && no.protectsMemory
  | .loop _ body => body.protectsMemory

theorem Executes.protectsMemory {input : List Bool} {tape : ℕ→Bool} {code : Code}
    {cost : ℕ} {s t : Store} (run : Executes input tape code cost s t) (hp : code.protectsMemory=true) :
    t.val.memory=s.val.memory := by
  induction run with
  | skip => rfl
  | call body s t cost steps _ => exact steps.protectsMemory hp
  | seq _ _ ih1 ih2 =>
    simp only [Code.protectsMemory,Bool.and_eq_true] at hp
    exact (ih2 hp.2).trans (ih1 hp.1)
  | yes _ _ ih =>
    simp only [Code.protectsMemory,Bool.and_eq_true] at hp
    exact ih hp.1
  | no _ _ ih =>
    simp only [Code.protectsMemory,Bool.and_eq_true] at hp
    exact ih hp.2
  | done => rfl
  | more _ _ _ ih1 ih2 => exact (ih2 hp).trans (ih1 hp)
end Structured
end Maxwell.Cost
