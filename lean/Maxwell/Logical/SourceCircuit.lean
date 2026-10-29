import Maxwell.Logical.SourceRows
import Maxwell.Logical.DyadicSize
import Maxwell.Logical.CopiedResidual
import Maxwell.Logical.Decoder

namespace Maxwell.Logical

def sourceCircuit (S : Source.SparseSystem) (precision : ℕ) :=
  compileCopiedForest ((Normalization.sourceRows S precision).map rowExpression)

theorem sourceCircuit_size (S : Source.SparseSystem) (precision : ℕ) (hn : S.n ≤ S.nnz) :
    (sourceCircuit S precision).size ≤ 6 * S.nnz * (precision + 1) := by
  have h := dyadic_copied_forest_size (Normalization.sourceRows S precision) precision
    (Normalization.sourceRows_length S precision)
    (by simpa [Normalization.sourceRows_term_count] using hn)
    (fun row hr term ht => (Normalization.sourceRows_precision S precision row hr term ht).le)
  simpa [Normalization.sourceRows_term_count, sourceCircuit] using h

theorem sourceCircuit_output_count (S : Source.SparseSystem) (precision : ℕ) :
    (sourceCircuit S precision).outputs.length = S.n := by
  unfold sourceCircuit
  rw [compileCopiedForest_output_count]
  simp

def sourceOutput (S : Source.SparseSystem) (precision : ℕ) :
    Fin S.n → Fin (sourceCircuit S precision).size := fun i =>
  (sourceCircuit S precision).outputs.get ⟨i.val, by
    rw [sourceCircuit_output_count]
    exact i.isLt⟩

def roundedProduct (S : Source.SparseSystem) (precision : ℕ) (input : Fin S.n → ℝ) :
    Fin S.n → ℝ := fun i =>
  ∑ j, ((Rounding.matrix precision (Normalization.normalizedMatrix S) i j : ℚ) : ℝ) * input j

theorem sourceRowList_correct (S : Source.SparseSystem) (hm : 2 ≤ S.nnz)
    (precision : ℕ) (hs : 1 ≤ precision) (input : Fin S.n → ℝ) :
    (((Normalization.sourceRows S precision).map rowExpression).map
      (fun e => e.evaluate input)) = List.ofFn (roundedProduct S precision input) := by
  simp only [Normalization.sourceRows, List.map_ofFn, Function.comp_def]
  apply congrArg List.ofFn
  funext i
  exact Normalization.rowTerms_matrix_semantics S hm precision hs i input

theorem sourceCircuit_correct (S : Source.SparseSystem) (hm : 2 ≤ S.nnz)
    (precision : ℕ) (hs : 1 ≤ precision) (input : Fin S.n → ℝ) :
    (sourceCircuit S precision).outputs.map ((sourceCircuit S precision).circuit.evaluate input 0) =
      List.ofFn (roundedProduct S precision input) := by
  unfold sourceCircuit
  rw [compileCopiedForest_correct, sourceRowList_correct S hm precision hs input]

theorem sourceOutput_correct (S : Source.SparseSystem) (hm : 2 ≤ S.nnz)
    (precision : ℕ) (hs : 1 ≤ precision) (input : Fin S.n → ℝ) (i : Fin S.n) :
    (sourceCircuit S precision).circuit.evaluate input 0 (sourceOutput S precision i) =
      roundedProduct S precision input i := by
  have h := sourceCircuit_correct S hm precision hs input
  have hi : i.val < ((sourceCircuit S precision).outputs.map
      ((sourceCircuit S precision).circuit.evaluate input 0)).length := by
    simp only [List.length_map, sourceCircuit_output_count]
    exact i.isLt
  have hv := getElem_congr h (rfl : i.val = i.val) hi
  simpa [sourceOutput] using hv

/-- Original input coordinates and the exact rational undo-normalization
factor are already concrete at the circuit stage. Later graph transforms
must preserve and transport this map. -/
def sourceCircuitDecoder (S : Source.SparseSystem) (precision : ℕ) :
    DecoderPlan S.n (sourceCircuit S precision).size where
  coordinate := (sourceCircuit S precision).circuit.inputIndex
  scale := Normalization.sourceScale S / Normalization.matrixScale S

theorem sourceCircuit_arbitrary_residual (S : Source.SparseSystem) (hm : 2 ≤ S.nnz)
    (precision : ℕ) (hs : 1 ≤ precision) (input : Fin S.n → ℝ)
    (state : Fin (sourceCircuit S precision).size → ℝ) (E : ℝ) (hE : 0 ≤ E)
    (he : ∀ j, |(sourceCircuit S precision).circuit.residual input state j| ≤ E) :
    List.Forall₂ (fun output value => |state output - value| ≤
      (((sourceCircuit S precision).size : ℝ) + 1) ^ 2 * E)
      (sourceCircuit S precision).outputs (List.ofFn (roundedProduct S precision input)) := by
  have h := compileCopiedForest_arbitrary_residual
    ((Normalization.sourceRows S precision).map rowExpression)
    (by
      intro e he
      obtain ⟨terms, _, rfl⟩ := List.mem_map.mp he
      exact rowExpression_bounded terms) input state E hE he
  rw [sourceRowList_correct S hm precision hs input] at h
  exact h

end Maxwell.Logical
