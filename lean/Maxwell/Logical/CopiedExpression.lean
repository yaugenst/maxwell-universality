import Maxwell.Logical.CopyBank
import Maxwell.Logical.Linearize
import Maxwell.Logical.CompileResidual

namespace Maxwell.Logical

def occurrenceCopies {n : ℕ} (e : Expression n) :=
  CopyBank.allocate (CopyBank.initial n) e.occurrences

def copiedInputs {n : ℕ} (e : Expression n) :
    Fin e.leafCount → Fin (occurrenceCopies e).bank.size := fun i =>
  (occurrenceCopies e).outputs.get ⟨i.val, by
    rw [(occurrenceCopies e).output_count, e.occurrences_length]
    exact i.isLt⟩

theorem copiedInputs_injective {n : ℕ} (e : Expression n) :
    Function.Injective (copiedInputs e) := by
  intro i j h
  have hi := (occurrenceCopies e).output_nodup.injective_get h
  exact Fin.ext (congrArg (fun k : Fin (occurrenceCopies e).outputs.length => k.val) hi)

theorem copiedInputs_unused {n : ℕ} (e : Expression n) (i : Fin e.leafCount) :
    (occurrenceCopies e).bank.circuit.uses (copiedInputs e i) = 0 := by
  apply (occurrenceCopies e).output_unused
  exact List.get_mem _ _

theorem copiedInputs_correct {n : ℕ} (e : Expression n) (input : Fin n → ℝ)
    (i : Fin e.leafCount) :
    (occurrenceCopies e).bank.circuit.evaluate input 0 (copiedInputs e i) =
      input (e.leafSource i) := by
  have h := (occurrenceCopies e).correct input
  have h' := h.trans (congrArg (List.map input) e.leafSource_list.symm)
  have hi : i.val < ((occurrenceCopies e).outputs.map
      ((occurrenceCopies e).bank.circuit.evaluate input 0)).length := by
    simp only [List.length_map, (occurrenceCopies e).output_count, e.occurrences_length]
    exact i.isLt
  have hv := getElem_congr h' (rfl : i.val = i.val) hi
  simpa [copiedInputs] using hv

/-- The constructed copy bank feeds distinct unused leaves to the actual
arithmetic compiler; all original input repetitions have been eliminated. -/
def compileCopiedExpression {n : ℕ} (e : Expression n) :=
  compileExpression e.linearized (occurrenceCopies e).bank.circuit (copiedInputs e)

theorem compileCopiedExpression_correct {n : ℕ} (e : Expression n) (input : Fin n → ℝ) :
    (compileCopiedExpression e).circuit.evaluate input 0 (compileCopiedExpression e).output =
      e.evaluate input := by
  rw [(compileCopiedExpression e).correct]
  have hi : (fun i => (occurrenceCopies e).bank.circuit.evaluate input 0 (copiedInputs e i)) =
      (fun i => input (e.leafSource i)) := by
    funext i
    exact copiedInputs_correct e input i
  rw [hi, e.linearized_evaluate]

theorem compileCopiedExpression_size {n : ℕ} (e : Expression n) :
    (compileCopiedExpression e).size = n + 2 * e.leafCount + e.gateCount := by
  rw [(compileCopiedExpression e).allocation, e.linearized_gateCount,
    (occurrenceCopies e).allocation, e.occurrences_length]
  rfl

end Maxwell.Logical
