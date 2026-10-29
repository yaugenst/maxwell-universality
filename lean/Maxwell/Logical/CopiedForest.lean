import Maxwell.Logical.CopyBank
import Maxwell.Logical.ForestLinearize

namespace Maxwell.Logical

def forestCopies {n : ℕ} (rows : List (Expression n)) :=
  CopyBank.allocate (CopyBank.initial n) (List.ofFn (forestSources rows))

def copiedForestInputs {n : ℕ} (rows : List (Expression n)) :
    Fin (forestLeafCount rows) → Fin (forestCopies rows).bank.size := fun i =>
  (forestCopies rows).outputs.get ⟨i.val, by
    rw [(forestCopies rows).output_count, List.length_ofFn]
    exact i.isLt⟩

theorem copiedForestInputs_injective {n : ℕ} (rows : List (Expression n)) :
    Function.Injective (copiedForestInputs rows) := by
  intro i j h
  have hi := (forestCopies rows).output_nodup.injective_get h
  exact Fin.ext (congrArg (fun k : Fin (forestCopies rows).outputs.length => k.val) hi)

theorem copiedForestInputs_unused {n : ℕ} (rows : List (Expression n))
    (i : Fin (forestLeafCount rows)) :
    (forestCopies rows).bank.circuit.uses (copiedForestInputs rows i) = 0 := by
  apply (forestCopies rows).output_unused
  exact List.get_mem _ _

theorem copiedForestInputs_correct {n : ℕ} (rows : List (Expression n)) (input : Fin n → ℝ)
    (i : Fin (forestLeafCount rows)) :
    (forestCopies rows).bank.circuit.evaluate input 0 (copiedForestInputs rows i) =
      input (forestSources rows i) := by
  have h := (forestCopies rows).correct input
  have hi : i.val < ((forestCopies rows).outputs.map
      ((forestCopies rows).bank.circuit.evaluate input 0)).length := by
    simp only [List.length_map, (forestCopies rows).output_count, List.length_ofFn]
    exact i.isLt
  have hv := getElem_congr h (rfl : i.val = i.val) hi
  simpa [copiedForestInputs] using hv

/-- One actual copy bank for the entire matrix, followed by all rows.
Every expression variable is one distinct copy leaf. -/
def compileCopiedForest {n : ℕ} (rows : List (Expression n)) :=
  compileForest (linearizedRows rows) (forestCopies rows).bank.circuit (copiedForestInputs rows)

theorem compileCopiedForest_correct {n : ℕ} (rows : List (Expression n)) (input : Fin n → ℝ) :
    (compileCopiedForest rows).outputs.map ((compileCopiedForest rows).circuit.evaluate input 0) =
      rows.map (fun e => e.evaluate input) := by
  rw [(compileCopiedForest rows).correct]
  have hi : (fun i => (forestCopies rows).bank.circuit.evaluate input 0 (copiedForestInputs rows i)) =
      (fun i => input (forestSources rows i)) := by
    funext i
    exact copiedForestInputs_correct rows input i
  rw [hi, linearizedRows_evaluate]

theorem compileCopiedForest_size {n : ℕ} (rows : List (Expression n)) :
    (compileCopiedForest rows).size = n + 2 * forestLeafCount rows +
      (rows.map Expression.gateCount).sum := by
  rw [(compileCopiedForest rows).allocation, linearizedRows_gateCounts,
    (forestCopies rows).allocation, List.length_ofFn]
  rfl

theorem compileCopiedForest_output_count {n : ℕ} (rows : List (Expression n)) :
    (compileCopiedForest rows).outputs.length = rows.length := by
  rw [(compileCopiedForest rows).output_count]
  have h := congrArg List.length (linearizedRows_gateCounts rows)
  simpa using h

end Maxwell.Logical
