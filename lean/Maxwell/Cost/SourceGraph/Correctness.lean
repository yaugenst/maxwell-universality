import Maxwell.Cost.SourceGraph.Positive
import Maxwell.Cost.PositiveGraph.Invariant.DiagonalSource

namespace Maxwell.Cost.SourceGraph.Positive
open PositiveGraph

theorem Result.clock {S : Source.SparseSystem} {p : ℕ} {s : Structured.Store} (h : Result S p s) :
    ∃ bits, bits.length=width S p+3 ∧ BankArray.Word s.val 146 bits := by
  obtain ⟨previous,hr,hf⟩ := h.saved
  obtain ⟨sourceClock,endpointClock,diagonalClock,hd⟩ := (Positive.from_retained hr).descriptor
  exact ⟨endpointClock,hd.endpointClock_length,
    BankArray.word_of_eq (hf.tapes 146 (by decide) (by decide)) hd.endpointClock⟩

theorem Result.diagonal {S : Source.SparseSystem} {p : ℕ} {s : Structured.Store} (h : Result S p s) :
    BitArray.Represents s.val.memory (base S p) 4 (Invariant.sourceDiagonalWords S p) := by
  have he := h.graph.diagonal
  rw [tables,Invariant.source_diagonal_exact (width S p) S p (initialTables S p) rfl] at he
  exact he

/-- The two arrays constructed by the actual source program represent
the literal routed-graph inputs, rather than an unrelated graph with
matching dimensions. -/
theorem Result.graph_arrays {S : Source.SparseSystem} {p : ℕ} {s : Structured.Store} (h : Result S p s) :
    BitArray.Represents s.val.memory 0 (width S p+3) (Invariant.sourceEndpointWords (width S p) S p) ∧
    BitArray.Represents s.val.memory (base S p) 4 (Invariant.sourceDiagonalWords S p) :=
  ⟨h.endpoints,h.diagonal⟩

end Maxwell.Cost.SourceGraph.Positive
