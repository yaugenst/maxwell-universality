import Maxwell.Cost.SourceGraph.PassReady

namespace Maxwell.Cost.SourceGraph.Positive
open Structured SourceCircuit PositiveGraph
open RationalAccumulator (Word Blank word_of_eq blank_of_eq)

def tables (S : Source.SparseSystem) (p : ℕ) :=
  Invariant.sourceTables (width S p) S p (initialTables S p)
def code (k c : ℕ) : Code := .seq (Retained.code k c) Pass.code
def passBudget (S : Source.SparseSystem) (p : ℕ) :=
  375000000*(count S p+1)*(width S p+1)^2
noncomputable def totalBudget (p : Source.Parameters) (S : Source.SparseSystem) (k c : ℕ) : ℕ :=
  Retained.totalBudget p S k c+passBudget S (Realization.binaryCoefficientPrecision S.nnz k c)

structure Result (S : Source.SparseSystem) (p : ℕ) (s : Store) : Prop where
  room : dimension S p < 2^width S p
  data : Retain.Data S p s.val
  numeric : Metadata.Numeric (width S p) (dimension S p) (count S p) s.val
  graph : (tables S p).Represents (width S p) (base S p) s.val.memory
  counters : BitArray.Represents s.val.memory (4*count S p*(width S p+3)) 2
    (Initialize.constantWords (2*dimension S p+count S p) 2 0)
  ranks : BitArray.Represents s.val.memory (4*count S p*(width S p+3)+2*(2*dimension S p+count S p)) 2
    (Initialize.constantWords (4*count S p) 2 0)
  workspace : Workspace s.val
  saved : ∃ previous : Store, Retained.Result S p previous ∧ PositiveGraph.Frame workBanks previous.val s.val

theorem Result.endpoints {S : Source.SparseSystem} {p : ℕ} {s : Store} (h : Result S p s) :
    BitArray.Represents s.val.memory 0 (width S p+3) (Invariant.sourceEndpointWords (width S p) S p) := by
  have he := h.graph.endpoints
  rw [tables,Invariant.source_endpoints_exact (width S p) S p h.room (initialTables S p)] at he
  exact he

theorem Result.fresh {S : Source.SparseSystem} {p : ℕ} {s : Store} (h : Result S p s)
    (i : ℕ) (hi : 163 ≤ i) (hret : i < 500 ∨ 509 < i) : s.val.tapes i=BitTape.blank := by
  obtain ⟨previous,hr,hf⟩ := h.saved
  exact (hf.tapes i (Or.inr (by omega)) (by simp [workBanks]; omega)).trans
    (hr.fresh i (by omega) (Or.inr hi) hret)

theorem Result.io {S : Source.SparseSystem} {p : ℕ} {s : Store} (h : Result S p s) :
    s.val.inputHead=(Codec.source S).length ∧ s.val.randomCursor=0 ∧ s.val.output=[] := by
  obtain ⟨previous,hr,hf⟩ := h.saved
  exact ⟨hf.inputHead.trans hr.io.1,hf.randomCursor.trans hr.io.2.1,hf.output.trans hr.io.2.2⟩

/-- The sparse archive is read once. Its endpoint and diagonal writes are
bound to the actual source graph, with routing counters and ranks preserved. -/
theorem emit (S : Source.SparseSystem) (p : ℕ) (input : List Bool) (tape : ℕ → Bool)
    (s : Store) (hs : Retained.Result S p s) :
    ∃ cost t, Executes input tape Pass.code cost s t ∧ cost ≤ passBudget S p ∧ Result S p t := by
  have hr := Positive.from_retained hs
  obtain ⟨sourceClock,endpointClock,diagonalClock,hd⟩ := hr.descriptor
  have hk : count S p ≤ 3*dimension S p := Logical.sourceSquareEntries_length_le S p
  have ht : (initialTables S p).Represents (width S p) (base S p) s.val.memory :=
    ⟨hr.arrays.endpoints,hr.arrays.diagonals⟩
  obtain ⟨cost,t,hcost,et,_source,tm,tablesOK,_descriptor,_cursors,tw,tf⟩ := Pass.executes input tape
    (width S p) (dimension S p) (count S p) (base S p) (Invariant.sourceRecords S p)
    sourceClock endpointClock diagonalClock s (Invariant.sourceRecords_length S p) hk hr.room
    (by dsimp [base]; omega) hd hr.workspace hr.left hr.right hr.mediator
    hr.numeric.edges hr.numeric.doubledDimension (initialTables S p) ht hr.archive
  have numeric := hr.numeric.transport (fun i hlo _ _ => tf.tapes i (Or.inr (by omega))
    (by simp [workBanks]; omega))
  have data : Retain.Data S p t.val :=
    ⟨hs.data.numeric.transport (fun i hlo _ _ _ => tf.tapes i (Or.inr (by omega))
      (by simp [workBanks]; omega)),
      word_of_eq (tf.tapes 503 (by decide) (by decide)) hs.data.circuitSize,
      (tf.tapes 508 (by decide) (by decide)).trans hs.data.rhs⟩
  refine ⟨cost,t,et,hcost.trans (Pass.price_packed_le (width S p) (dimension S p) (count S p) hr.room hk),
    hr.room,data,numeric,tablesOK,?_,?_,tw,⟨s,hs,tf⟩⟩
  · rw [tm]
    exact foldMemory_preserves hr.arrays.counters (width S p) (dimension S p) (count S p) 0
      (base S p) (Invariant.sourceRecords S p) (by exact le_of_eq ((Nat.zero_add _).trans (Invariant.sourceRecords_length S p))) (initialTables S p)
      (by dsimp [IncidenceEncoding.Separated]; omega)
      (by dsimp [IncidenceEncoding.Separated,base]; omega)
  · rw [tm]
    exact foldMemory_preserves hr.arrays.ranks (width S p) (dimension S p) (count S p) 0
      (base S p) (Invariant.sourceRecords S p) (by exact le_of_eq ((Nat.zero_add _).trans (Invariant.sourceRecords_length S p))) (initialTables S p)
      (by dsimp [IncidenceEncoding.Separated]; omega)
      (by dsimp [IncidenceEncoding.Separated,base]; omega)

set_option maxRecDepth 16384 in
theorem executes (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (hb : S.source ≠ 0)
    (k c : ℕ) (tape : ℕ → Bool) :
    ∃ cost t, Executes (Codec.source S) tape (code k c) cost (Store.ofState BitRAMState.initial) t ∧
      cost ≤ totalBudget p S k c ∧ Result S (Realization.binaryCoefficientPrecision S.nnz k c) t := by
  obtain ⟨rcost,s,es,hrc,hs⟩ := Retained.executes p S hp hm hb k c tape
  obtain ⟨cost,t,et,hcost,ht⟩ := emit S _ (Codec.source S) tape s hs
  exact ⟨rcost+cost,t,es.seq et,Nat.add_le_add hrc hcost,ht⟩

def program (k c : ℕ) : BitRAM := (code k c).compile

theorem run (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (hb : S.source ≠ 0)
    (k c : ℕ) (tape : ℕ → Bool) :
    ∃ t : Store, ((program k c).run (Codec.source S) tape (totalBudget p S k c+1)).finished =
        some (t.place (code k c).size) ∧
      ((program k c).run (Codec.source S) tape (totalBudget p S k c+1)).instructions ≤ totalBudget p S k c ∧
      Result S (Realization.binaryCoefficientPrecision S.nnz k c) t := by
  obtain ⟨cost,t,he,hcost,ht⟩ := executes p S hp hm hb k c tape
  have hr := he.compiled_run (totalBudget p S k c+1) (by omega)
  exact ⟨t,hr.1,hr.2.symm ▸ hcost,ht⟩

end Maxwell.Cost.SourceGraph.Positive
