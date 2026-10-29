import Maxwell.Logical.SourceCircuit
import Maxwell.Cost.SourceCircuit.ArithmeticTrace
import Maxwell.Cost.SourceCircuit.ArithmeticMarkers
import Maxwell.Cost.SourceCircuit.ArithmeticPrelude
import Maxwell.Cost.SourceCircuit.AllocateSource.Correspondence

namespace Maxwell.Cost.SourceCircuit.CompileSourceInitial
open Logical
open Structured

/-- The copied-forest input function enumerates the allocation outputs in
exactly their stored preorder, including their dependent finite bounds. -/
theorem copiedForestInputs_list {n : ℕ} (expressions : List (Expression n)) :
    List.ofFn (copiedForestInputs expressions) = (forestCopies expressions).outputs := by
  have length : (forestCopies expressions).outputs.length = forestLeafCount expressions := by
    rw [(forestCopies expressions).output_count,List.length_ofFn]
  have h := List.ofFn_congr length (forestCopies expressions).outputs.get
  rw [List.ofFn_get] at h
  exact h.symm

theorem initial_next (S : Source.SparseSystem) (p : ℕ) (roots : RootInitData S.n)
    (memory : ℕ → Bool) (allocated : Store) (ha : AllocateSource.Result S p roots memory allocated) :
    addressValue (ArithmeticPrelude.data S p roots memory).next =
      (forestCopies ((Normalization.sourceRows S p).map Logical.rowExpression)).bank.size := by
  change addressValue (AllocateSource.finalData S p roots memory).next = _
  rw [ha.represented.next,AllocateSource.bank_eq_forestCopies]

theorem initial_gates (S : Source.SparseSystem) (p : ℕ) (roots : RootInitData S.n)
    (memory : ℕ → Bool) (allocated : Store) (ha : AllocateSource.Result S p roots memory allocated) :
    traceBytes (InitializeMetadata.width S.nnz p)
      ((CopyBank.initial S.n).trace
        (List.ofFn (forestSources ((Normalization.sourceRows S p).map Logical.rowExpression)))) =
      some (ArithmeticPrelude.data S p roots memory).gates := by
  change traceBytes _ _ = some (AllocateSource.finalData S p roots memory).gates
  rw [ha.gates,← AllocateSource.requests_eq_forestSources]
  exact ha.trace

theorem initial_leaves (S : Source.SparseSystem) (p : ℕ) (roots : RootInitData S.n)
    (memory : ℕ → Bool) (allocated : Store) (ha : AllocateSource.Result S p roots memory allocated) :
    (ArithmeticPrelude.data S p roots memory).leaves.map addressValue =
      (List.ofFn (copiedForestInputs
        ((Normalization.sourceRows S p).map Logical.rowExpression))).map Fin.val := by
  have room : (AllocateSource.bank S p).bank.size < 2^(InitializeMetadata.width S.nnz p) := by
    have hr := ha.valid.room
    rw [ha.represented.next] at hr
    simpa [AllocationPass.occurrences] using hr
  rw [copiedForestInputs_list,← AllocateSource.outputs_eq_forestCopies]
  simp only [ArithmeticPrelude.data,ArithmeticPrelude.leafWords,List.map_map]
  apply List.map_congr_left
  intro i _
  exact fixedWidth_value _ i.val (i.isLt.trans room)

theorem sourceOutput_list (S : Source.SparseSystem) (p : ℕ) :
    List.ofFn (fun i : Fin S.n => (Logical.sourceOutput S p i).val) =
      (sourceCircuit S p).outputs.map Fin.val := by
  have h := List.ofFn_congr (sourceCircuit_output_count S p) (sourceCircuit S p).outputs.get
  rw [List.ofFn_get] at h
  have outputs : List.ofFn (Logical.sourceOutput S p) = (sourceCircuit S p).outputs := h.symm
  rw [← outputs,List.map_ofFn]
  rfl

end Maxwell.Cost.SourceCircuit.CompileSourceInitial
