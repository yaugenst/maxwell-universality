import Maxwell.Cost.Structured.Rename

namespace Maxwell.Cost.RoutingPorts.Size
open Structured

/-- Routing size selection has a private copy of the geometric-search
banks and its rational comparison workspace. -/
def shiftBank (i : ℕ) : ℕ :=
  if 520 ≤ i ∧ i ≤ 527 then i+180 else
  if 700 ≤ i ∧ i ≤ 707 then i-180 else
  if 30 ≤ i ∧ i ≤ 36 then i+710 else
  if 740 ≤ i ∧ i ≤ 746 then i-710 else i

theorem shiftBank_involutive : Function.Involutive shiftBank := by
  intro i
  simp only [shiftBank]
  split_ifs <;> omega

def relocation : Equiv.Perm ℕ := ⟨shiftBank,shiftBank,shiftBank_involutive,shiftBank_involutive⟩

@[simp] theorem relocation_apply (i : ℕ) : relocation i=shiftBank i := rfl
@[simp] theorem relocation_symm_apply (i : ℕ) : relocation.symm i=shiftBank i := rfl

@[simp] theorem renamed_tape (s : Store) (i : ℕ) :
    (s.renameTapes relocation.symm).val.tapes i=s.val.tapes (shiftBank i) := rfl

theorem shiftBank_fixed (i : ℕ) (h₁ : i < 30 ∨ 36< i) (h₂ : i < 520 ∨ 527< i)
    (h₃ : i < 700 ∨ 707< i) (h₄ : i < 740 ∨ 746< i) : shiftBank i=i := by
  simp only [shiftBank]
  split_ifs <;> omega

end Maxwell.Cost.RoutingPorts.Size
