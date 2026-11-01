import Maxwell.Cost.SourceGraph.Retain.Core

/-! Retained source data depends only on its ten owned tape addresses. -/
namespace Maxwell.Cost.SourceGraph.Retain

theorem Data.transport {S : Source.SparseSystem} {p : ℕ} {s t : BitRAMState}
    (h : Data S p s) (keep : ∀i,500 ≤ i→i≤509→t.tapes i=s.tapes i) : Data S p t :=
  ⟨h.numeric.transport (fun i lo hi _ _=>keep i lo hi),
    RationalAccumulator.word_of_eq (keep 503 (by decide) (by decide)) h.circuitSize,
    (keep 508 (by decide) (by decide)).trans h.rhs⟩

#print axioms Data.transport
end Maxwell.Cost.SourceGraph.Retain
