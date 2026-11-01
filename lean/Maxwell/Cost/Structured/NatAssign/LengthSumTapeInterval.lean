import Maxwell.Cost.Structured.NatAssign.LengthSum
import Maxwell.Cost.Structured.NatAssign.TapeInterval

/-! Tape preservation for measured width allocation, including source
lists presented abstractly rather than evaluated by the kernel. -/
namespace Maxwell.Cost
open Structured

theorem WordLength.outsideTapes (source target lo hi : ℕ)
    (hs : source<lo ∨hi ≤ source) (ht : target<lo ∨hi ≤ target) :
    (code source target).outsideTapes lo hi=true := by
  simp [code,program,Increment.program,Rewind.program,Code.outsideTapes,BitRAM.outsideTapes,
    BitRAMInstruction.outsideTapes,BitRAMInstruction.relocate,hs,ht]

namespace Structured.NatAssign.LengthSum

theorem code_outside (target temp lo hi : ℕ) (sources : List ℕ) (low : 4 ≤ lo)
    (ht : target<lo ∨hi ≤ target) (hu : temp<lo ∨hi ≤ temp) (ne : temp≠target)
    (hs : ∀i∈sources,i<lo ∨hi ≤ i) : (code target temp sources).outsideTapes lo hi=true := by
  induction sources with
  | nil => rfl
  | cons source rest ih =>
    simp only [code,Code.outsideTapes,Bool.and_eq_true]
    refine ⟨WordLength.outsideTapes source temp lo hi (hs source (by simp)) hu,?_,
      ih (fun i hi=>hs i (List.mem_cons_of_mem _ hi))⟩
    apply NatAssign.code_outside (combine target temp) {target,temp} lo hi
      (by simp [combine,Instruction.Valid,ne]) low
    intro i hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl <;> assumption

theorem initializedCode_outside (target temp bias lo hi : ℕ) (sources : List ℕ) (low : 4 ≤ lo)
    (ht : target<lo ∨hi ≤ target) (hu : temp<lo ∨hi ≤ temp) (ne : temp≠target)
    (hs : ∀i∈sources,i<lo ∨hi ≤ i) : (initializedCode target temp bias sources).outsideTapes lo hi=true := by
  simp only [initializedCode,Code.outsideTapes,Bool.and_eq_true]
  refine ⟨?_,code_outside target temp lo hi sources low ht hu ne hs⟩
  apply NatAssign.code_outside (initialPlan target temp bias) {target,temp} lo hi
    (by simp [initialPlan,Instruction.Valid]) low
  intro i hi
  simp only [Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl <;> assumption

#print axioms initializedCode_outside
end Structured.NatAssign.LengthSum
end Maxwell.Cost
