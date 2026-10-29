import Maxwell.Cost.Structured.Syntax

/-! A finite syntactic footprint certifies exact preservation of a work tape. -/
namespace Maxwell.Cost

def BitRAMInstruction.protectsTape (workTape : ℕ) : BitRAMInstruction → Bool
  | .writeTape target _ | .eraseTape target | .tapeLeft target | .tapeRight target => decide (target ≠ workTape)
  | _ => true

def BitRAM.protectsTape (body : BitRAM) (workTape : ℕ) : Bool :=
  body.code.all (BitRAMInstruction.protectsTape workTape)

theorem BitRAM.protectsTape_next {body : BitRAM} {workTape : ℕ}
    (hp : body.protectsTape workTape = true) (input : List Bool) (randomTape : ℕ → Bool)
    (s t : BitRAMState) (extra : ℕ) (hn : body.next input randomTape s = some ⟨t,extra⟩) :
    t.tapes workTape = s.tapes workTape := by
  cases hi : body.code[s.pc]? with
  | none => simp [BitRAM.next,hi] at hn
  | some instruction =>
    have hs := List.all_eq_true.mp hp instruction (List.mem_of_getElem? hi)
    cases instruction <;>
      simp only [BitRAM.next,hi,Option.some.injEq,PricedStep.mk.injEq,BitRAMInstruction.protectsTape,
        decide_eq_true_eq] at hn hs <;>
      first
      | contradiction
      | rcases hn with ⟨rfl,rfl⟩
        simp_all [BitRAMState.setTape,BitRAMState.setRegister,ne_comm]

theorem PricedSteps.protectsTape {body : BitRAM} {workTape cost : ℕ}
    {input : List Bool} {randomTape : ℕ → Bool} {s t : BitRAMState}
    (run : PricedSteps (body.next input randomTape) cost s t)
    (hp : body.protectsTape workTape = true) : t.tapes workTape = s.tapes workTape :=
  run.conserved (fun s => s.tapes workTape) (body.protectsTape_next hp input randomTape)

namespace Structured

def Code.protectsTape (workTape : ℕ) : Code → Bool
  | .skip => true
  | .call body => body.protectsTape workTape
  | .seq first second => first.protectsTape workTape && second.protectsTape workTape
  | .branch _ yes no => yes.protectsTape workTape && no.protectsTape workTape
  | .loop _ body => body.protectsTape workTape

/-- Checking literal program syntax suffices to preserve the complete tape,
including its head and every blank or occupied cell, on every actual run. -/
theorem Executes.protectsTape {input : List Bool} {randomTape : ℕ → Bool}
    {code : Code} {cost : ℕ} {s t : Store} (run : Executes input randomTape code cost s t)
    (workTape : ℕ) (hp : code.protectsTape workTape = true) :
    t.val.tapes workTape = s.val.tapes workTape := by
  induction run with
  | skip => rfl
  | call body s t cost steps _ => exact steps.protectsTape hp
  | seq _ _ ih1 ih2 =>
    simp only [Code.protectsTape,Bool.and_eq_true] at hp
    exact (ih2 hp.2).trans (ih1 hp.1)
  | yes _ _ ih =>
    simp only [Code.protectsTape,Bool.and_eq_true] at hp
    exact ih hp.1
  | no _ _ ih =>
    simp only [Code.protectsTape,Bool.and_eq_true] at hp
    exact ih hp.2
  | done => rfl
  | more _ _ _ ih1 ih2 => exact (ih2 hp).trans (ih1 hp)

end Structured
end Maxwell.Cost
