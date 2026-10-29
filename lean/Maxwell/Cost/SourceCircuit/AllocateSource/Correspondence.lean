import Maxwell.Cost.SourceCircuit.AllocateSource.Grouping
import Maxwell.Cost.SourceCircuit.AllocateSource

namespace Maxwell.Cost.SourceCircuit.AllocateSource
open Logical

theorem horner_occurrences {n : ℕ} (i : Fin n) (bits : List Bool) :
    (Horner.expression i bits).occurrences = List.replicate (bits.count true) i := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    cases b <;> simp [Horner.expression,Expression.occurrences,ih,List.replicate_succ]

theorem term_occurrences {n : ℕ} (term : DyadicTerm n) :
    term.expression.occurrences = List.replicate (term.bits.count true) term.input := by
  cases hb : term.negative <;>
    simp [DyadicTerm.expression,hb,Expression.occurrences,horner_occurrences]

theorem row_occurrences {n : ℕ} (terms : List (DyadicTerm n)) :
    (rowExpression terms).occurrences =
      terms.flatMap (fun t => List.replicate (t.bits.count true) t.input) := by
  induction terms with
  | nil => rfl
  | cons t ts ih => simp [rowExpression,Expression.occurrences,term_occurrences,ih]

theorem rows_occurrences {n : ℕ} (rows : List (List (DyadicTerm n))) :
    ((rows.map rowExpression).map Expression.occurrences).flatten =
      rows.flatten.flatMap (fun t => List.replicate (t.bits.count true) t.input) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simpa [List.flatMap_append,row_occurrences] using congrArg
      (List.append (row.flatMap fun t => List.replicate (t.bits.count true) t.input)) ih

/-- The actual forward coefficient-stream requests are exactly the leaf
order used by the paper's source circuit, not merely a permutation. -/
theorem requests_eq_forestSources (S : Source.SparseSystem) (p : ℕ) :
    AllocationPass.requests (records S p) =
      List.ofFn (forestSources ((Normalization.sourceRows S p).map rowExpression)) := by
  rw [forestSources_list,rows_occurrences,sourceRows_flatten]
  simp only [AllocationPass.requests,records,List.flatMap_map]

theorem bank_eq_forestCopies (S : Source.SparseSystem) (p : ℕ) :
    (bank S p).bank = (forestCopies ((Normalization.sourceRows S p).map rowExpression)).bank := by
  unfold bank forestCopies
  rw [requests_eq_forestSources]

theorem outputs_eq_forestCopies (S : Source.SparseSystem) (p : ℕ) :
    (bank S p).outputs.map Fin.val =
      (forestCopies ((Normalization.sourceRows S p).map rowExpression)).outputs.map Fin.val := by
  unfold bank forestCopies
  rw [requests_eq_forestSources]

end Maxwell.Cost.SourceCircuit.AllocateSource
