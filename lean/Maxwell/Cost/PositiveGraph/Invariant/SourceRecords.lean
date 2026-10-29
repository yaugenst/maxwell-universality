import Maxwell.Cost.PositiveGraph.Fold
import Maxwell.Composition.SourceCached

namespace Maxwell.Cost.PositiveGraph.Invariant

def sourceRecords (S : Source.SparseSystem) (p : ℕ) :
    List (BoundedEntry (Logical.sourceCircuit S p).size) :=
  (Logical.sourceSquareEntries S p).attach.map fun e =>
    ⟨e.val,(Logical.sourceCircuit_rational S p).code.squareEntries_bounded
      (Logical.sourceOutput S p) e.val e.property⟩

@[simp] theorem sourceRecords_length (S : Source.SparseSystem) (p : ℕ) :
    (sourceRecords S p).length=(Logical.sourceSquareEntries S p).length := by simp [sourceRecords]

@[simp] theorem sourceRecords_get (S : Source.SparseSystem) (p : ℕ)
    (j : ℕ) (hj : j<(sourceRecords S p).length) :
    (sourceRecords S p)[j].val = (Logical.sourceSquareEntries S p)[j]'(by simpa using hj) := by
  simp [sourceRecords]

@[simp] theorem sourceRecords_map (S : Source.SparseSystem) (p : ℕ) :
    (sourceRecords S p).map Subtype.val=Logical.sourceSquareEntries S p := by simp [sourceRecords,List.map_map]

end Maxwell.Cost.PositiveGraph.Invariant
