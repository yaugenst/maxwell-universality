import Maxwell.Cost.Structured.Rename

/-! A fixed permutation moves a finite tape bank into a disjoint interval.
This lets a shared finite program run beside an encoder's retained data. -/
namespace Maxwell.Cost.Structured.TapeBlockSwap

def index (base count gap i : ℕ) : ℕ :=
  if base≤ i ∧ i<base+count then i+gap
  else if base+gap≤ i ∧ i<base+gap+count then i-gap else i

theorem involutive (base count gap : ℕ) (separated : count≤gap) :
    Function.Involutive (index base count gap) := by
  intro i
  unfold index
  split_ifs <;> omega

def permutation (base count gap : ℕ) (separated : count≤gap) : Equiv.Perm ℕ :=
  Function.Involutive.toPerm _ (involutive base count gap separated)

@[simp] theorem apply_inside (base count gap : ℕ) (separated : count≤gap) (i : ℕ)
    (lo : base≤ i) (hi : i<base+count) : permutation base count gap separated i=i+gap := by
  exact ite_eq_left ⟨lo,hi⟩

@[simp] theorem apply_outside (base count gap : ℕ) (separated : count≤gap) (i : ℕ)
    (original : i<base ∨ base+count≤ i) (destination : i<base+gap ∨ base+gap+count≤ i) :
    permutation base count gap separated i=i := by
  change index base count gap i=i
  simp only [index]
  split_ifs <;> omega

@[simp] theorem symm (base count gap : ℕ) (separated : count≤gap) :
    (permutation base count gap separated).symm=permutation base count gap separated := rfl

#print axioms involutive
end Maxwell.Cost.Structured.TapeBlockSwap
