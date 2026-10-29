import Maxwell.Cost.Structured.Rename
import Maxwell.Cost.PositiveGraph.Metadata

namespace Maxwell.Cost.GraphIncidence
open Structured

/-- A fixed exchange moves the incidence work banks to untouched tapes600–612.
It is applied to literal program operands before any input is read. -/
def shiftBank (i : ℕ) : ℕ :=
  if 80 ≤ i ∧ i ≤ 92 then i+520 else if 600 ≤ i ∧ i ≤ 612 then i-520 else i

theorem shiftBank_involutive : Function.Involutive shiftBank := by
  intro i
  simp only [shiftBank]
  split_ifs <;> omega

def relocation : Equiv.Perm ℕ := ⟨shiftBank,shiftBank,shiftBank_involutive,shiftBank_involutive⟩

@[simp] theorem relocation_apply (i : ℕ) : relocation i=shiftBank i := rfl
@[simp] theorem relocation_symm_apply (i : ℕ) : relocation.symm i=shiftBank i := rfl

theorem shiftBank_old (i : ℕ) (hi : 80 ≤ i) (hj : i ≤ 92) : shiftBank i=i+520 := by simp [shiftBank,hi,hj]
theorem shiftBank_new (i : ℕ) (hi : 600 ≤ i) (hj : i ≤ 612) : shiftBank i=i-520 := by
  simp [shiftBank,hi,hj,show ¬i≤92 by omega]
theorem shiftBank_fixed (i : ℕ) (hi : i < 80 ∨ 92 < i) (hj : i < 600 ∨ 612 < i) : shiftBank i=i := by
  simp only [shiftBank]
  split_ifs <;> omega

@[simp] theorem renamed_tape (s : Store) (i : ℕ) :
    (s.renameTapes relocation.symm).val.tapes i=s.val.tapes (shiftBank i) := rfl

/-- Source graph metadata occupies a disjoint persistent range. -/
theorem numeric_renamed (width dimension count : ℕ) (s : Store)
    (h : PositiveGraph.Metadata.Numeric width dimension count s.val) :
    PositiveGraph.Metadata.Numeric width dimension count (s.renameTapes relocation.symm).val := by
  apply PositiveGraph.Metadata.Numeric.transport h
  intro i hi hj _
  change s.val.tapes (shiftBank i)=s.val.tapes i
  rw [shiftBank_fixed i (by omega) (by omega)]

end Maxwell.Cost.GraphIncidence
