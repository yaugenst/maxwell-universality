import Maxwell.Cost.Structured.Footprint

/-! A finite code check protects every tape above a fixed boundary. -/
namespace Maxwell.Cost

def BitRAMInstruction.tapesBelow (bound : ℕ) : BitRAMInstruction→Bool
  | .writeTape target _ | .eraseTape target | .tapeLeft target | .tapeRight target => decide (target<bound)
  | _ => true

def BitRAM.tapesBelow (body : BitRAM) (bound : ℕ) : Bool :=
  body.code.all (BitRAMInstruction.tapesBelow bound)

theorem BitRAMInstruction.tapesBelow_protects {instruction : BitRAMInstruction} {bound workTape : ℕ}
    (h : instruction.tapesBelow bound=true) (hk : bound≤workTape) :
    instruction.protectsTape workTape=true := by
  cases instruction <;> simp only [tapesBelow,protectsTape,decide_eq_true_eq] at h ⊢ <;> omega

theorem BitRAM.tapesBelow_protects {body : BitRAM} {bound workTape : ℕ}
    (h : body.tapesBelow bound=true) (hk : bound≤workTape) : body.protectsTape workTape=true := by
  apply List.all_eq_true.mpr
  intro instruction hi
  exact BitRAMInstruction.tapesBelow_protects (List.all_eq_true.mp h instruction hi) hk

namespace Structured

def Code.tapesBelow (bound : ℕ) : Code→Bool
  | .skip => true
  | .call body => body.tapesBelow bound
  | .seq first second => first.tapesBelow bound && second.tapesBelow bound
  | .branch _ yes no => yes.tapesBelow bound && no.tapesBelow bound
  | .loop _ body => body.tapesBelow bound

theorem Code.tapesBelow_protects {code : Code} {bound workTape : ℕ}
    (h : code.tapesBelow bound=true) (hk : bound≤workTape) : code.protectsTape workTape=true := by
  induction code with
  | skip => rfl
  | call body => exact body.tapesBelow_protects h hk
  | seq a b ha hb =>
    simp only [tapesBelow,Bool.and_eq_true] at h
    simp only [protectsTape,Bool.and_eq_true]
    exact ⟨ha h.1,hb h.2⟩
  | branch _ a b ha hb =>
    simp only [tapesBelow,Bool.and_eq_true] at h
    simp only [protectsTape,Bool.and_eq_true]
    exact ⟨ha h.1,hb h.2⟩
  | loop _ body ih => exact ih h

theorem Executes.tapesBelow {input : List Bool} {tape : ℕ→Bool} {code : Code} {cost bound : ℕ}
    {s t : Store} (run : Executes input tape code cost s t) (h : code.tapesBelow bound=true)
    (i : ℕ) (hi : bound ≤ i) : t.val.tapes i=s.val.tapes i :=
  run.protectsTape i (Code.tapesBelow_protects h hi)

end Structured
#print axioms Structured.Executes.tapesBelow
end Maxwell.Cost
