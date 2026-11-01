import Maxwell.Cost.Structured.NatAssign.Bounds

/-! Values and widths of fixed natural-word programs, independent of the
physical construction that supplies their operands. -/

namespace Maxwell.Cost.Structured.NatAssign

theorem values_width (ids : Finset ℕ) (instructions : List Instruction)
    (hv : ∀ a ∈ instructions, a.Valid ids) (v : ℕ→ℕ) (B : ℕ)
    (hb : ∀ i ∈ ids, (v i).bits.length≤B)
    (hc : ∀ a ∈ instructions, a.literalWidth≤B) :
    ∀ i ∈ ids, (values instructions v i).bits.length+1≤2^instructions.length*(B+1) := by
  induction instructions generalizing v B with
  | nil => intro i hi;simpa [values] using Nat.add_le_add_right (hb i hi) 1
  | cons a rest ih =>
    have h := ih (fun a ha => hv a (by simp [ha])) (a.update v) (2*B+1)
      (instruction_width ids a (hv a (by simp)) v B hb (hc a (by simp)))
      (fun a ha => (hc a (by simp [ha])).trans (by omega))
    intro i hi
    simpa only [values,List.length_cons,pow_succ,show 2*B+1+1=2*(B+1) by ring,
      Nat.mul_assoc] using h i hi

theorem values_congr (ids : Finset ℕ) (instructions : List Instruction)
    (hv : ∀ a ∈ instructions, a.Valid ids) (v w : ℕ→ℕ)
    (he : ∀ i ∈ ids, v i=w i) : ∀ i ∈ ids, values instructions v i=values instructions w i := by
  induction instructions generalizing v w with
  | nil => exact he
  | cons a rest ih =>
    apply ih (fun b hb => hv b (by simp [hb]))
    have ha := hv a (by simp)
    have hva : a.value v=a.value w := by
      cases a with
      | literal target n => rfl
      | copy source target => exact he source ha.1
      | add source target => exact congrArg₂ (·+·) (he source ha.1) (he target ha.2.1)
      | multiply source target => exact congrArg₂ (·*·) (he source ha.1) (he target ha.2.1)
    intro i hi
    by_cases ht : i=a.target
    · subst i;simpa only [Instruction.update,Function.update_self] using hva
    · simpa only [Instruction.update,Function.update_of_ne ht] using he i hi

theorem values_append (xs ys : List Instruction) (v : ℕ→ℕ) :
    values (xs++ys) v=values ys (values xs v) := by
  induction xs generalizing v with
  | nil => rfl
  | cons x xs ih => exact ih (x.update v)

/-- Reset a finite set of words to specified literals. Repeated targets are
harmless because each occurrence writes the same value. -/
theorem values_literals (targets : List ℕ) (w v : ℕ→ℕ) (i : ℕ) :
    values (targets.map fun j => Instruction.literal j (w j)) v i =
      if i∈targets then w i else v i := by
  induction targets generalizing v with
  | nil => simp [values]
  | cons j rest ih =>
    simp only [List.map_cons,values,ih,List.mem_cons]
    by_cases hr : i∈rest
    · simp [hr]
    · by_cases hj : i=j
      · subst i;simp [hr,Instruction.update,Instruction.target,Instruction.value]
      · simp [hr,hj,Instruction.update,Instruction.target,Instruction.value]

/-- A fixed instruction list preserves every word it never targets. -/
theorem values_preserves (instructions : List Instruction) (v : ℕ→ℕ) (i : ℕ)
    (keep : ∀a∈instructions,i≠a.target) : values instructions v i=v i := by
  induction instructions generalizing v with
  | nil => rfl
  | cons a rest ih =>
    change values rest (a.update v) i=v i
    rw [ih (a.update v) (fun b hb=>keep b (by simp [hb]))]
    exact Function.update_of_ne (keep a (by simp)) _ _

theorem values_outside (ids : Finset ℕ) (instructions : List Instruction)
    (hv : ∀ a ∈ instructions, a.Valid ids) (v : ℕ→ℕ) (i : ℕ) (hi : i∉ids) :
    values instructions v i=v i := by
  induction instructions generalizing v with
  | nil => rfl
  | cons a rest ih =>
    have ha := hv a (by simp)
    have ht : a.target∈ids := by
      cases a with
      | literal target n => exact ha
      | copy source target | add source target | multiply source target => exact ha.2.1
    have hne : i≠a.target := fun h => hi (h ▸ ht)
    change values rest (a.update v) i=v i
    rw [ih (fun b hb => hv b (by simp [hb]))]
    exact Function.update_of_ne hne _ _


/-- Copy and literal assignments preserve a common word-width bound. -/
def Instruction.AssignmentBound (B : ℕ) : Instruction→Prop
  | .literal _ n => n.bits.length ≤ B
  | .copy _ _ => True
  | _ => False

theorem values_assignment_width (ids : Finset ℕ) (instructions : List Instruction)
    (hv : ∀a∈instructions,a.Valid ids) (v : ℕ→ℕ) (B : ℕ)
    (hb : ∀i∈ids,(v i).bits.length ≤ B)
    (ha : ∀a∈instructions,a.AssignmentBound B) :
    ∀i∈ids,(values instructions v i).bits.length ≤ B := by
  induction instructions generalizing v with
  | nil => exact hb
  | cons a rest ih =>
    apply ih (fun x hx=>hv x (by simp [hx]))
      (a.update v) ?_ (fun x hx=>ha x (by simp [hx]))
    intro i hi
    by_cases ht : i=a.target
    · subst i
      simp only [Instruction.update,Function.update_self]
      have hav := hv a (by simp)
      have haa := ha a (by simp)
      cases a with
      | literal target n => exact haa
      | copy source target => exact hb source hav.1
      | add source target | multiply source target => exact False.elim haa
    · simpa only [Instruction.update,Function.update_of_ne ht] using hb i hi

#print axioms values_width
#print axioms values_congr

end Maxwell.Cost.Structured.NatAssign
