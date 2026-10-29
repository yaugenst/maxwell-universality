import Maxwell.Cost.SourceGraph.Prepare
import Maxwell.Cost.SourceSquare.ExactRhs

namespace Maxwell.Cost.SourceGraph.Prepare
open Structured
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

/-- Computing the actual graph metadata preserves the original rational
RHS archive for the physical source serializer. -/
theorem exact_rhs (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (k c : ℕ) (tape : ℕ → Bool)
    {cost : ℕ} {t : Store}
    (he : Executes (Codec.source S) tape (code k c) cost
      (Store.ofState BitRAMState.initial) t) :
    t.val.tapes 20 = BitTape.ofList (LogRats.records (List.ofFn S.source)) := by
  cases he with
  | seq square suffix =>
    exact (suffix.protectsTape 20 (by decide)).trans (SourceSquare.exact_rhs p S hp hm k c tape square)

/-- The exact archive and the graph preparation output belong to one
executed program, with its existing charged source-only budget. -/
theorem executes_with_rhs (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (hb : S.source ≠ 0)
    (k c : ℕ) (tape : ℕ → Bool) :
    ∃ cost t, Executes (Codec.source S) tape (code k c) cost
      (Store.ofState BitRAMState.initial) t ∧ cost ≤ totalBudget p S k c ∧
      Result S (Realization.binaryCoefficientPrecision S.nnz k c) t ∧
      t.val.tapes 20 = BitTape.ofList (LogRats.records (List.ofFn S.source)) := by
  obtain ⟨cost,t,he,hcost,ht⟩ := executes p S hp hm hb k c tape
  exact ⟨cost,t,he,hcost,ht,exact_rhs p S hp hm k c tape he⟩

end Maxwell.Cost.SourceGraph.Prepare
