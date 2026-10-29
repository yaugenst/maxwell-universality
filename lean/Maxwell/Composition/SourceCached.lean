import Maxwell.Composition.SourceEnumeration

/-! Cached sparse-entry lookup for the positive graph. The sparse list is
converted to one vector before an endpoint callback is constructed, so every
incidence query reads the saved array rather than traversing the entry list. -/

namespace Maxwell.Composition.SourceCached

open Maxwell.Logical

/-- Materialize the emitted sparse-entry list exactly once. -/
def entries (S : Source.SparseSystem) (precision : ℕ) :
    Vector RationalCode.Entry (sourceSquareEntries S precision).length :=
  ⟨(sourceSquareEntries S precision).toArray, by simp⟩

@[simp] theorem entries_get (S : Source.SparseSystem) (precision : ℕ)
    (i : Fin (sourceSquareEntries S precision).length) :
    (entries S precision).get i = SourceEnumeration.entry S precision i := by
  simp [entries, Vector.get, Fin.cast, SourceEnumeration.entry]

/-- Return an array-backed coordinate-pair callback, sharing one entry vector. -/
def pair (S : Source.SparseSystem) (precision : ℕ) :
    Fin (sourceSquareEntries S precision).length →
      Fin (sourceCircuit S precision).size × Fin (sourceCircuit S precision).size :=
  let saved := entries S precision
  fun i =>
    let e := saved.get i
    have he : e ∈ sourceSquareEntries S precision := by
      rw [show e = SourceEnumeration.entry S precision i from entries_get S precision i]
      exact SourceEnumeration.entry_mem S precision i
    let hb := (sourceCircuit_rational S precision).code.squareEntries_bounded
      (sourceOutput S precision) e he
    (⟨e.row, hb.1⟩, ⟨e.column, hb.2⟩)

@[simp] theorem pair_eq (S : Source.SparseSystem) (precision : ℕ)
    (i : Fin (sourceSquareEntries S precision).length) :
    pair S precision i = SourceEnumeration.pair S precision i := by
  apply Prod.ext <;> apply Fin.ext <;>
    simp only [pair, SourceEnumeration.pair, entries_get]

/-- All arithmetic dimensions and the pair lookup are arguments to the
callback constructor, so queries reuse the prepared dimensions as well. -/
def endpointFromPairs (dimension count : ℕ)
    (saved : Fin count → Fin dimension × Fin dimension) :
    Fin (count + count) → Bool → Fin (dimension + dimension + count) :=
  fun i side =>
    match finSumFinEquiv.symm i with
    | Sum.inl k =>
        if side then finSumFinEquiv (Sum.inr k)
        else finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inl (saved k).1)))
    | Sum.inr k =>
        if side then finSumFinEquiv (Sum.inr k)
        else finSumFinEquiv (Sum.inl (finSumFinEquiv (Sum.inr (saved k).2)))

/-- Build the positive-edge endpoint callback from the saved pair lookup.
No sparse-list traversal occurs inside an incidence query. -/
def positiveEndpoint (S : Source.SparseSystem) (precision : ℕ) :
    Fin ((sourceSquareEntries S precision).length + (sourceSquareEntries S precision).length) →
      Bool → Fin ((sourceCircuit S precision).size + (sourceCircuit S precision).size +
        (sourceSquareEntries S precision).length) :=
  let saved := pair S precision
  endpointFromPairs (sourceCircuit S precision).size (sourceSquareEntries S precision).length saved

@[simp] theorem positiveEndpoint_eq (S : Source.SparseSystem) (precision : ℕ)
    (i : Fin ((sourceSquareEntries S precision).length + (sourceSquareEntries S precision).length))
    (side : Bool) : positiveEndpoint S precision i side =
      SourceEnumeration.positiveEndpoint S precision i side := by
  cases hi : finSumFinEquiv.symm i <;> cases side <;>
    simp only [positiveEndpoint, endpointFromPairs, SourceEnumeration.positiveEndpoint, hi, pair_eq,
      Bool.false_eq_true, ↓reduceIte]

theorem positiveEndpoint_correct (S : Source.SparseSystem) (precision : ℕ)
    (i : Fin ((sourceSquareEntries S precision).length + (sourceSquareEntries S precision).length))
    (side : Bool) :
    positiveEndpoint S precision i side = SourceEnumeration.vertexEquiv S precision
      (if side then (SourcePositive.graph S precision).head
          ((SourceEnumeration.positiveEdgeEquiv S precision).symm i)
        else (SourcePositive.graph S precision).tail
          ((SourceEnumeration.positiveEdgeEquiv S precision).symm i)) := by
  rw [positiveEndpoint_eq]
  exact SourceEnumeration.positiveEndpoint_correct S precision i side

end Maxwell.Composition.SourceCached
