import Maxwell.Cost.Structured.NatAssign.Values

/-! A fixed exponent is a finite list of stored-word multiplications.
The base is read from the input bank; only the exponent belongs to the code. -/
namespace Maxwell.Cost.Structured.NatAssign

def powerInstructions (source target exponent : ℕ) : List Instruction :=
  .literal target 1::List.replicate exponent (.multiply source target)

theorem multiply_replicate (source target exponent : ℕ) (different : source≠target) (v : ℕ→ℕ) :
    values (List.replicate exponent (.multiply source target)) v=
      Function.update v target ((v source)^exponent*v target) := by
  induction exponent generalizing v with
  | zero => simp [values]
  | succ n ih =>
    rw [List.replicate_succ]
    simp only [values]
    rw [ih]
    funext i
    by_cases hi : i=target
    · subst i
      simp [Instruction.update,Instruction.value,Instruction.target,different,pow_succ]
      ring
    · simp [Instruction.update,Instruction.value,Instruction.target,hi]

theorem power_values (source target exponent : ℕ) (different : source≠target) (v : ℕ→ℕ) :
    values (powerInstructions source target exponent) v=
      Function.update v target ((v source)^exponent) := by
  simp only [powerInstructions,values,multiply_replicate source target exponent different]
  funext i
  by_cases hi : i=target
  · subst i;simp [Instruction.update,Instruction.value,Instruction.target,different]
  · simp [Instruction.update,Instruction.value,Instruction.target,hi]

theorem power_valid (ids : Finset ℕ) (source target exponent : ℕ)
    (hs : source∈ids) (ht : target∈ids) (different : source≠target) :
    ∀a∈powerInstructions source target exponent,a.Valid ids := by
  intro a ha
  simp only [powerInstructions,List.mem_cons,List.mem_replicate] at ha
  rcases ha with rfl|⟨_,rfl⟩
  · exact ht
  · exact ⟨hs,ht,different⟩

theorem power_literalWidth (source target exponent : ℕ) :
    ∀a∈powerInstructions source target exponent,a.literalWidth≤1 := by
  intro a ha
  simp only [powerInstructions,List.mem_cons,List.mem_replicate] at ha
  rcases ha with rfl|⟨_,rfl⟩ <;> simp [Instruction.literalWidth]

#print axioms power_values
end Maxwell.Cost.Structured.NatAssign
