import Maxwell.Cost.Structured.WordCleanup
import Maxwell.Cost.Structured.TapeSet
import Maxwell.Cost.Structured.InputPositions

/-! Cleanup preserves every disjoint tape bank, including when its finite
clear list is produced by sorting a set instead of a literal list. -/
namespace Maxwell.Cost.Structured.WordCleanup

theorem code_protectsSet (clear : List ℕ) (kept : Finset ℕ)
    (outside : ∀i∈clear,i∉kept) : (code clear).protectsSet kept=true:=by
  induction clear with
  | nil => rfl
  | cons i rest ih =>
    have hi:=outside i (by simp)
    have tail:=ih (fun j hj=>outside j (List.mem_cons_of_mem _ hj))
    simp only [code,Code.protectsSet,tail,Bool.and_true]
    simp [BitRAM.protectsSet,TapeOps.clear,BitRAMInstruction.protectsSet,hi]

theorem code_inputPositions (clear : List ℕ) : (code clear).protectsInputPositions=true:=by
  induction clear with
  | nil => rfl
  | cons i rest ih =>
    simp only [code,Code.protectsInputPositions,ih,Bool.and_true]
    rfl

#print axioms code_protectsSet
end Maxwell.Cost.Structured.WordCleanup
