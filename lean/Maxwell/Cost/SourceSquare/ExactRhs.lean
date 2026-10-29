import Maxwell.Cost.SourceSquare
import Maxwell.Cost.Structured.Determinism
import Maxwell.Cost.Structured.Footprint

/-! Exact original source bytes survive the normalization and circuit
compiler. These invariants concern actual executions and complete tapes. -/
namespace Maxwell.Cost
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
open Structured

namespace NormalizeSource

/-- Every actual frontend execution retains the original rational RHS. -/
theorem frontend_exact_rhs (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (k c : ℕ) (tape : ℕ → Bool)
    {cost : ℕ} {t : Store}
    (he : Executes (Codec.source S) tape (frontendCode k c) cost
      (Store.ofState BitRAMState.initial) t) :
    t.val.tapes 20 = BitTape.ofList (LogRats.records (List.ofFn S.source)) := by
  obtain ⟨_,u,_,hu,_,hrhs⟩ := frontend_executes_with_rhs p S hp hm k c tape
  exact (hu.deterministic he).2 ▸ hrhs

/-- Normalizing the emitted RHS does not replace its original archive. -/
theorem exact_rhs (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (k c : ℕ) (tape : ℕ → Bool)
    {cost : ℕ} {t : Store}
    (he : Executes (Codec.source S) tape (code k c) cost
      (Store.ofState BitRAMState.initial) t) :
    t.val.tapes 20 = BitTape.ofList (LogRats.records (List.ofFn S.source)) := by
  cases he with
  | seq front rhs =>
    exact (rhs.protectsTape 20 (by decide)).trans (frontend_exact_rhs p S hp hm k c tape front)

end NormalizeSource

namespace SourceCircuit

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
theorem Preparation.exact_rhs (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (k c : ℕ) (tape : ℕ → Bool)
    {cost : ℕ} {t : Store}
    (he : Executes (Codec.source S) tape (Preparation.code k c) cost
      (Store.ofState BitRAMState.initial) t) :
    t.val.tapes 20 = BitTape.ofList (LogRats.records (List.ofFn S.source)) := by
  cases he with
  | seq normal suffix =>
    exact (suffix.protectsTape 20 (by decide)).trans (NormalizeSource.exact_rhs p S hp hm k c tape normal)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
theorem AllocateSource.exact_rhs (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (k c : ℕ) (tape : ℕ → Bool)
    {cost : ℕ} {t : Store}
    (he : Executes (Codec.source S) tape (AllocateSource.code k c) cost
      (Store.ofState BitRAMState.initial) t) :
    t.val.tapes 20 = BitTape.ofList (LogRats.records (List.ofFn S.source)) := by
  cases he with
  | seq pre suffix =>
    exact (suffix.protectsTape 20 (by decide)).trans (Preparation.exact_rhs p S hp hm k c tape pre)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
theorem ArithmeticPrelude.source_exact_rhs (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (k c : ℕ) (tape : ℕ → Bool)
    {cost : ℕ} {t : Store}
    (he : Executes (Codec.source S) tape (ArithmeticPrelude.sourceCode k c) cost
      (Store.ofState BitRAMState.initial) t) :
    t.val.tapes 20 = BitTape.ofList (LogRats.records (List.ofFn S.source)) := by
  cases he with
  | seq allocated suffix =>
    exact (suffix.protectsTape 20 (by decide)).trans (AllocateSource.exact_rhs p S hp hm k c tape allocated)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
theorem CompileSource.exact_rhs (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (k c : ℕ) (tape : ℕ → Bool)
    {cost : ℕ} {t : Store}
    (he : Executes (Codec.source S) tape (CompileSource.code k c) cost
      (Store.ofState BitRAMState.initial) t) :
    t.val.tapes 20 = BitTape.ofList (LogRats.records (List.ofFn S.source)) := by
  cases he with
  | seq pre suffix =>
    exact (suffix.protectsTape 20 (by decide)).trans (ArithmeticPrelude.source_exact_rhs p S hp hm k c tape pre)

end SourceCircuit

namespace SourceSquare

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
/-- The actual square-system encoder preserves the exact unrounded RHS on
work tape20, ready for the subsequent physical-source compiler. -/
theorem exact_rhs (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (k c : ℕ) (tape : ℕ → Bool)
    {cost : ℕ} {t : Store}
    (he : Executes (Codec.source S) tape (code k c) cost
      (Store.ofState BitRAMState.initial) t) :
    t.val.tapes 20 = BitTape.ofList (LogRats.records (List.ofFn S.source)) := by
  cases he with
  | seq pre suffix =>
    exact (suffix.protectsTape 20 (by decide)).trans (SourceCircuit.CompileSource.exact_rhs p S hp hm k c tape pre)

/-- The previous cost and output contract together with the exact retained
RHS, all witnessed by the same actual machine execution. -/
theorem executes_with_rhs (p : Source.Parameters) (S : Source.SparseSystem)
    (hp : Source.Promises p S) (hm : 2 ≤ S.nnz) (hb : S.source ≠ 0)
    (k c : ℕ) (tape : ℕ → Bool) :
    ∃ cost t, Executes (Codec.source S) tape (code k c) cost
      (Store.ofState BitRAMState.initial) t ∧ cost ≤ totalBudget p S k c ∧
      Result S (Realization.binaryCoefficientPrecision S.nnz k c) t ∧
      t.val.tapes 20 = BitTape.ofList (LogRats.records (List.ofFn S.source)) := by
  obtain ⟨cost,t,he,hcost,ht⟩ := executes p S hp hm hb k c tape
  exact ⟨cost,t,he,hcost,ht,exact_rhs p S hp hm k c tape he⟩

end SourceSquare
end Maxwell.Cost
