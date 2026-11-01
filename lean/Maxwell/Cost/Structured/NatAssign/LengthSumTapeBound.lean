import Maxwell.Cost.Structured.NatAssign.LengthSum
import Maxwell.Cost.Structured.NatAssignTapeBound

/-! Measuring a finite list of words touches only the listed sources and
the fixed length accumulator, independent of word contents and list order. -/
namespace Maxwell.Cost
open Structured

theorem WordLength.tapeBound (source target N : ℕ)
    (hs : source < N) (ht : target < N) : (code source target).tapeBound ≤ N := by
  simp [code,program,Increment.program,Rewind.program,Code.tapeBound,BitRAM.tapeBound,
    BitRAMInstruction.tapeBound,BitRAMInstruction.relocate]
  omega

namespace Structured.NatAssign.LengthSum

theorem code_tapeBound (target temp N : ℕ) (sources : List ℕ) (hN : 4 ≤ N)
    (ht : target < N) (hu : temp < N) (ne : temp ≠ target)
    (hs : ∀i∈sources,i < N) : (code target temp sources).tapeBound ≤ N := by
  induction sources with
  | nil => exact Nat.zero_le N
  | cons source rest ih =>
    refine max_le (WordLength.tapeBound source temp N (hs source (by simp)) hu) (max_le ?_ ?_)
    · apply NatAssign.code_tapeBound_le (combine target temp) {target,temp} N
        (by simp [combine,Instruction.Valid,ne]) hN
      intro i hi
      simp only [Finset.mem_insert,Finset.mem_singleton] at hi
      rcases hi with rfl|rfl <;> assumption
    · exact ih (fun i hi=>hs i (List.mem_cons_of_mem _ hi))

theorem initializedCode_tapeBound (target temp bias N : ℕ) (sources : List ℕ)
    (hN : 4 ≤ N) (ht : target < N) (hu : temp < N) (ne : temp ≠ target)
    (hs : ∀i∈sources,i < N) : (initializedCode target temp bias sources).tapeBound ≤ N := by
  refine max_le ?_ (code_tapeBound target temp N sources hN ht hu ne hs)
  apply NatAssign.code_tapeBound_le (initialPlan target temp bias) {target,temp} N
    (by simp [initialPlan,Instruction.Valid]) hN
  intro i hi
  simp only [Finset.mem_insert,Finset.mem_singleton] at hi
  rcases hi with rfl|rfl <;> assumption

#print axioms initializedCode_tapeBound
end Structured.NatAssign.LengthSum
end Maxwell.Cost
