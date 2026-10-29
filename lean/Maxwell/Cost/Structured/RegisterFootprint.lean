import Maxwell.Cost.Structured.Syntax

/-! A finite syntactic footprint certifies exact preservation of a Boolean register. -/
namespace Maxwell.Cost

def BitRAMInstruction.protectsRegister (register : ℕ) : BitRAMInstruction → Bool
  | .literal dst _ | .bitXor dst _ _ | .bitAnd dst _ _ | .bitNot dst _
  | .readSequential dst | .addressPeek dst | .addressIsEmpty dst
  | .readInput dst | .readMemory dst | .randomBit dst => decide (dst ≠ register)
  | .readTape _ value present => decide (value ≠ register ∧ present ≠ register)
  | _ => true

def BitRAM.protectsRegister (body : BitRAM) (register : ℕ) : Bool :=
  body.code.all (BitRAMInstruction.protectsRegister register)

theorem BitRAM.protectsRegister_next {body : BitRAM} {register : ℕ}
    (hp : body.protectsRegister register = true) (input : List Bool) (randomTape : ℕ → Bool)
    (s t : BitRAMState) (extra : ℕ) (hn : body.next input randomTape s = some ⟨t,extra⟩) :
    t.registers register = s.registers register := by
  cases hi : body.code[s.pc]? with
  | none => simp [BitRAM.next,hi] at hn
  | some instruction =>
    have hs := List.all_eq_true.mp hp instruction (List.mem_of_getElem? hi)
    cases instruction <;>
      simp only [BitRAM.next,hi,Option.some.injEq,PricedStep.mk.injEq,BitRAMInstruction.protectsRegister,
        decide_eq_true_eq] at hn hs <;>
      first
      | contradiction
      | rcases hn with ⟨rfl,rfl⟩
        simp_all [BitRAMState.setTape,BitRAMState.setRegister,ne_comm]

theorem PricedSteps.protectsRegister {body : BitRAM} {register cost : ℕ}
    {input : List Bool} {randomTape : ℕ → Bool} {s t : BitRAMState}
    (run : PricedSteps (body.next input randomTape) cost s t)
    (hp : body.protectsRegister register = true) : t.registers register = s.registers register :=
  run.conserved (fun s => s.registers register) (body.protectsRegister_next hp input randomTape)

namespace Structured

def Code.protectsRegister (register : ℕ) : Code → Bool
  | .skip => true
  | .call body => body.protectsRegister register
  | .seq first second => first.protectsRegister register && second.protectsRegister register
  | .branch _ yes no => yes.protectsRegister register && no.protectsRegister register
  | .loop _ body => body.protectsRegister register

/-- Checking literal program syntax suffices to preserve the selected Boolean register, on every actual run. -/
theorem Executes.protectsRegister {input : List Bool} {randomTape : ℕ → Bool}
    {code : Code} {cost : ℕ} {s t : Store} (run : Executes input randomTape code cost s t)
    (register : ℕ) (hp : code.protectsRegister register = true) :
    t.val.registers register = s.val.registers register := by
  induction run with
  | skip => rfl
  | call body s t cost steps _ => exact steps.protectsRegister hp
  | seq _ _ ih1 ih2 =>
    simp only [Code.protectsRegister,Bool.and_eq_true] at hp
    exact (ih2 hp.2).trans (ih1 hp.1)
  | yes _ _ ih =>
    simp only [Code.protectsRegister,Bool.and_eq_true] at hp
    exact ih hp.1
  | no _ _ ih =>
    simp only [Code.protectsRegister,Bool.and_eq_true] at hp
    exact ih hp.2
  | done => rfl
  | more _ _ _ ih1 ih2 => exact (ih2 hp).trans (ih1 hp)

end Structured
end Maxwell.Cost
