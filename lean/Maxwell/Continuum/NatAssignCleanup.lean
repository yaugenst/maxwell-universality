import Maxwell.Continuum.RationalDataflowBinaryValues

/-! Clearing a fixed finite list of work tapes has exact finite-bank
semantics. This helper is shared by repeated elementary evaluators. -/
namespace Maxwell.Cost.Structured.NatAssign

def clearList (xs : List ℕ) : List Instruction := xs.map (fun i => .literal i 0)

theorem clearList_values (xs : List ℕ) (v : ℕ→ℕ) (i : ℕ) :
    values (clearList xs) v i=if i∈xs then 0 else v i := by
  induction xs generalizing v with
  | nil => simp [clearList,values]
  | cons x xs ih =>
    simp only [clearList,List.map_cons,values]
    rw [show List.map (fun i => Instruction.literal i 0) xs=clearList xs by rfl,ih]
    by_cases hi : i∈xs
    · simp only [hi,List.mem_cons,or_true,ite_true]
    · by_cases he : i=x
      · subst i
        simp only [hi,List.mem_cons,true_or,ite_true,ite_false,Instruction.update,
          Instruction.target,Instruction.value,Function.update_self]
      · simp only [hi,he,List.mem_cons,false_or,ite_false,Instruction.update,
          Instruction.target,Instruction.value,Function.update_of_ne he]

theorem clearList_valid (S : Finset ℕ) (xs : List ℕ) (h : ∀i∈xs,i∈S) :
    ∀a∈clearList xs,a.Valid S := by
  intro a ha
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
  exact h i hi

theorem clearList_length (xs : List ℕ) : (clearList xs).length=xs.length := by simp [clearList]

theorem clearList_literalWidth (xs : List ℕ) : ∀a∈clearList xs,a.literalWidth=0 := by
  intro a ha
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
  rfl

#print axioms clearList_values
end Maxwell.Cost.Structured.NatAssign
