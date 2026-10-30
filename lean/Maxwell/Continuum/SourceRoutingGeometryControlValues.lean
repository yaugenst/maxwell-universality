import Maxwell.Continuum.SourceRoutingGeometryControlExecution

namespace Maxwell.Cost.RoutingPorts.Complete.GeometryArithmetic
open Structured
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

theorem Control.positive_true (source : ℕ) (yes no : Control) (v : ℕ→ℕ) (h : 0<v source) :
    (Control.positive source yes no).evaluate v=yes.evaluate v := ite_eq_left h
theorem Control.positive_false (source : ℕ) (yes no : Control) (v : ℕ→ℕ) (h : ¬0<v source) :
    (Control.positive source yes no).evaluate v=no.evaluate v := ite_eq_right h

theorem Control.evaluate_width (c : Control) (valid : c.Valid) (v : ℕ→ℕ) (B : ℕ)
    (width : ∀j∈ids,(v j).bits.length ≤ B) (literals : c.Literals B) :
    ∀j∈ids,(c.evaluate v j).bits.length+1 ≤ 2^c.steps*(B+1) := by
  induction c generalizing v B with
  | done => intro j hj;simpa only [Control.evaluate,Control.steps,pow_zero,one_mul] using Nat.add_le_add_right (width j hj) 1
  | assign a rest ih =>
    have wu:=NatAssign.instruction_width ids a (instruction_valid valid.1) v B width literals.1
    have h:=ih valid.2 (a.update v) (2*B+1) wu (literals.2.mono (by omega))
    intro j hj
    calc
      _ ≤ 2^rest.steps*(2*B+1+1) := h j hj
      _ = _ := by simp only [Control.steps,pow_add,pow_one];ring
  | divide source divisor quotient remainder rest ih =>
    have h:=ih valid.2.2.2.2.2 (divided v source divisor quotient remainder) B
      (divided_width v source divisor quotient remainder B (Finset.mem_union_left _ valid.1) width) literals
    intro j hj
    exact (h j hj).trans (Nat.mul_le_mul_right (B+1)
      (Nat.pow_le_pow_right (by decide) (by simp only [Control.steps];omega)))
  | decrement target rest ih =>
    have h:=ih valid.2 (Function.update v target (v target-1)) B
      (decrement_width v target B (Finset.mem_union_left _ valid.1) width) literals
    intro j hj
    exact (h j hj).trans (Nat.mul_le_mul_right (B+1)
      (Nat.pow_le_pow_right (by decide) (by simp only [Control.steps];omega)))
  | positive source yes no iy ino =>
    by_cases hp : 0<v source
    · intro j hj
      simp only [Control.evaluate,hp,ite_true]
      exact (iy valid.2.1 v B width literals.1 j hj).trans (Nat.mul_le_mul_right (B+1)
        (Nat.pow_le_pow_right (by decide) (by simp only [Control.steps];omega)))
    · intro j hj
      simp only [Control.evaluate,hp,ite_false]
      exact (ino valid.2.2 v B width literals.2 j hj).trans (Nat.mul_le_mul_right (B+1)
        (Nat.pow_le_pow_right (by decide) (by simp only [Control.steps];omega)))

theorem Control.evaluate_zero (c : Control) (valid : c.Valid) (v : ℕ→ℕ)
    (zero : ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,v j=0) :
    ∀j∈Maxwell.Continuum.RationalDataflow.NaturalQuotient.workPorts,c.evaluate v j=0 := by
  induction c generalizing v with
  | done => exact zero
  | assign a rest ih => exact ih valid.2 _ (instruction_zero valid.1 v zero)
  | divide source divisor quotient remainder rest ih =>
    exact ih valid.2.2.2.2.2 _ (divided_zero v source divisor quotient remainder valid.2.2.1 valid.2.2.2.1 zero)
  | decrement target rest ih => exact ih valid.2 _ (decrement_zero v target valid.1 zero)
  | positive source yes no iy ino =>
    by_cases hp : 0<v source
    · simpa only [Control.evaluate,hp,ite_true] using iy valid.2.1 v zero
    · simpa only [Control.evaluate,hp,ite_false] using ino valid.2.2 v zero

theorem Control.prepend_steps (instructions : List NatAssign.Instruction) (rest : Control) :
    (Control.prepend instructions rest).steps=instructions.length+rest.steps := by
  induction instructions with
  | nil => simp [Control.prepend]
  | cons a xs ih =>
    simp only [Control.prepend,List.foldr_cons,Control.steps,List.length_cons] at *
    omega

theorem Control.prepend_evaluate (instructions : List NatAssign.Instruction) (rest : Control) (v : ℕ→ℕ) :
    (Control.prepend instructions rest).evaluate v=rest.evaluate (NatAssign.values instructions v) := by
  induction instructions generalizing v with
  | nil => rfl
  | cons a xs ih => exact ih (a.update v)

#print axioms Control.evaluate_width
end Maxwell.Cost.RoutingPorts.Complete.GeometryArithmetic
