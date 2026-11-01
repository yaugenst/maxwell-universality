import Maxwell.Cost.Structured.NatAssign.Values

/-! Integer arithmetic for a bracket with a common denominator. The four
numerator channels allow signed endpoints; no rational reduction is needed.
The midpoint occupies offsets6..8 and the two endpoints offsets0..5. -/
namespace Maxwell.Cost.Structured.SignedBracket
open NatAssign

def ids (base : ℕ) : Finset ℕ := Finset.Ico base (base+12)

def midpointPlan (b : ℕ) : List NatAssign.Instruction :=
  [.copy b (b+6),.add (b+3) (b+6),.copy (b+1) (b+7),.add (b+4) (b+7),
   .copy (b+2) (b+8),.literal (b+9) 2,.multiply (b+9) (b+8)]

def stepPlan (b : ℕ) (negative : Bool) : List NatAssign.Instruction :=
  if negative then
    [.literal (b+9) 31,.copy b (b+10),.multiply (b+9) (b+10),
     .copy (b+1) (b+11),.multiply (b+9) (b+11),.literal (b+9) 33,
     .multiply (b+9) (b+3),.multiply (b+9) (b+4),.add (b+10) (b+3),.add (b+11) (b+4),
     .literal (b+9) 64,.multiply (b+9) b,.multiply (b+9) (b+1),
     .multiply (b+9) (b+2),.copy (b+2) (b+5)]
  else
    [.literal (b+9) 31,.copy (b+3) (b+10),.multiply (b+9) (b+10),
     .copy (b+4) (b+11),.multiply (b+9) (b+11),.literal (b+9) 33,
     .multiply (b+9) b,.multiply (b+9) (b+1),.add (b+10) b,.add (b+11) (b+1),
     .literal (b+9) 64,.multiply (b+9) (b+3),.multiply (b+9) (b+4),
     .multiply (b+9) (b+2),.copy (b+2) (b+5)]

theorem ids_lower (b : ℕ) (hb : 4≤b) : ∀i∈ids b,4≤ i := by
  intro i hi
  simp only [ids,Finset.mem_Ico] at hi
  omega

theorem midpoint_valid (b : ℕ) : ∀a∈midpointPlan b,a.Valid (ids b) := by
  simp [midpointPlan,NatAssign.Instruction.Valid,ids]

theorem step_valid (b : ℕ) (negative : Bool) : ∀a∈stepPlan b negative,a.Valid (ids b) := by
  cases negative <;> simp [stepPlan,NatAssign.Instruction.Valid,ids]

theorem midpoint_literals (b : ℕ) : ∀a∈midpointPlan b,a.literalWidth≤7 := by
  simp only [midpointPlan,List.mem_cons,List.not_mem_nil,or_false]
  intro a ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [Instruction.literalWidth] <;> decide +kernel

theorem step_literals (b : ℕ) (negative : Bool) : ∀a∈stepPlan b negative,a.literalWidth≤7 := by
  cases negative <;> simp only [stepPlan,Bool.false_eq_true,ite_false,ite_true,
    List.mem_cons,List.not_mem_nil,or_false] <;>
    intro a ha <;>
    rcases ha with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp only [Instruction.literalWidth] <;> decide +kernel

theorem midpoint_changes (b : ℕ) : changes (midpointPlan b)⊆{0,1,2,3}∪ids b := by
  intro i hi
  simp only [changes,midpointPlan,List.map_cons,List.map_nil,List.toFinset_cons,List.toFinset_nil,
    NatAssign.Instruction.target,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,
    Finset.notMem_empty,or_false,ids,Finset.mem_Ico] at hi ⊢
  omega

theorem step_changes (b : ℕ) (negative : Bool) : changes (stepPlan b negative)⊆{0,1,2,3}∪ids b := by
  intro i hi
  cases negative <;>
    simp only [changes,stepPlan,Bool.false_eq_true,ite_false,ite_true,List.map_cons,List.map_nil,
      List.toFinset_cons,List.toFinset_nil,NatAssign.Instruction.target,Finset.mem_union,
      Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false,ids,Finset.mem_Ico] at hi ⊢ <;> omega

end Maxwell.Cost.Structured.SignedBracket
