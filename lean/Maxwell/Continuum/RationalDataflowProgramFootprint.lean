import Maxwell.Cost.Structured.Footprint

/-! One finite syntax check certifies a bank of preserved tapes without
rechecking the entire fixed program separately for every tape. -/
namespace Maxwell.Cost

def BitRAMInstruction.protectsSet (S : Finset ℕ) : BitRAMInstruction→Bool
  | .writeTape target _ | .eraseTape target | .tapeLeft target | .tapeRight target => decide (target∉S)
  | _ => true

def BitRAM.protectsSet (body : BitRAM) (S : Finset ℕ) : Bool :=
  body.code.all (BitRAMInstruction.protectsSet S)

theorem BitRAMInstruction.protectsSet_tape (instruction : BitRAMInstruction) (S : Finset ℕ)
    (h : instruction.protectsSet S=true) (i : ℕ) (hi : i∈S) : instruction.protectsTape i=true := by
  cases instruction <;> simp only [protectsSet,protectsTape,decide_eq_true_eq] at h ⊢
  all_goals intro he;subst i;exact h hi

theorem BitRAM.protectsSet_tape (body : BitRAM) (S : Finset ℕ) (h : body.protectsSet S=true)
    (i : ℕ) (hi : i∈S) : body.protectsTape i=true := by
  apply List.all_eq_true.mpr
  intro instruction hin
  exact instruction.protectsSet_tape S (List.all_eq_true.mp h instruction hin) i hi

namespace Structured

def Code.protectsSet (S : Finset ℕ) : Code→Bool
  | .skip => true
  | .call body => body.protectsSet S
  | .seq first second => first.protectsSet S && second.protectsSet S
  | .branch _ yes no => yes.protectsSet S && no.protectsSet S
  | .loop _ body => body.protectsSet S

theorem Code.protectsSet_tape (code : Code) (S : Finset ℕ) (h : code.protectsSet S=true)
    (i : ℕ) (hi : i∈S) : code.protectsTape i=true := by
  induction code with
  | skip => rfl
  | call body => exact body.protectsSet_tape S h i hi
  | seq first second ih1 ih2 =>
    simp only [protectsSet,Bool.and_eq_true] at h
    simp only [protectsTape,Bool.and_eq_true]
    exact ⟨ih1 h.1,ih2 h.2⟩
  | branch test yes no ih1 ih2 =>
    simp only [protectsSet,Bool.and_eq_true] at h
    simp only [protectsTape,Bool.and_eq_true]
    exact ⟨ih1 h.1,ih2 h.2⟩
  | loop test body ih => exact ih h

theorem Executes.protectsSet {input : List Bool} {tape : ℕ→Bool} {code : Code}
    {cost : ℕ} {s t : Store} (e : Executes input tape code cost s t)
    (S : Finset ℕ) (h : code.protectsSet S=true) (i : ℕ) (hi : i∈S) :
    t.val.tapes i=s.val.tapes i := e.protectsTape i (code.protectsSet_tape S h i hi)

#print axioms Executes.protectsSet
end Structured
end Maxwell.Cost
