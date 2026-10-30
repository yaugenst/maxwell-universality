import Maxwell.Cost.Structured.NatAssign

/-! A fixed register program ignores a separately stored runtime word when
that word is outside its declared input/output registers. -/
namespace Maxwell.Cost.Structured.NatAssign
set_option maxHeartbeats 1500000

theorem Instruction.value_update_outside (S : Finset ℕ) (a : Instruction) (ha : a.Valid S)
    (v : ℕ→ℕ) (p x : ℕ) (hp : p∉S) : a.value (Function.update v p x)=a.value v := by
  cases a with
  | literal t y => rfl
  | copy s t =>
    exact Function.update_of_ne (by intro h;subst s;exact hp ha.1) _ _
  | add s t =>
    simp only [Instruction.value,Function.update_of_ne
      (show s≠p from fun h => hp (h ▸ ha.1)),Function.update_of_ne
      (show t≠p from fun h => hp (h ▸ ha.2.1))]
  | multiply s t =>
    simp only [Instruction.value,Function.update_of_ne
      (show s≠p from fun h => hp (h ▸ ha.1)),Function.update_of_ne
      (show t≠p from fun h => hp (h ▸ ha.2.1))]

theorem Instruction.update_outside (S : Finset ℕ) (a : Instruction) (ha : a.Valid S)
    (v : ℕ→ℕ) (p x : ℕ) (hp : p∉S) :
    a.update (Function.update v p x)=Function.update (a.update v) p x := by
  have ht : a.target∈S := by cases a <;> first | exact ha | exact ha.2.1
  have hne : a.target≠p := fun h => hp (h ▸ ht)
  unfold Instruction.update
  rw [Instruction.value_update_outside S a ha v p x hp]
  exact (Function.update_comm hne _ _ _).symm

theorem values_update_outside (S : Finset ℕ) (ins : List Instruction)
    (hi : ∀a∈ins,a.Valid S) (v : ℕ→ℕ) (p x : ℕ) (hp : p∉S) :
    values ins (Function.update v p x)=Function.update (values ins v) p x := by
  induction ins generalizing v with
  | nil => rfl
  | cons a rest ih =>
    simp only [values]
    rw [Instruction.update_outside S a (hi a (by simp)) v p x hp]
    exact ih (fun b hb => hi b (by simp [hb])) _

#print axioms values_update_outside
end Maxwell.Cost.Structured.NatAssign
