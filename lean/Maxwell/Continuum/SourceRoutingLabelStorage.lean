import Maxwell.Continuum.SourceRoutingTreeStorage
import Maxwell.Cost.ColorAssemble.Correctness

/-! The assembled machine labels equal the logical recursive routing
colors, including their row-count scaling and harmless index casts. -/

namespace Maxwell.Cost.RoutingPorts.Complete.Tree
open Maxwell.Logical.Routing Coloring Coloring.NumericSplit
set_option maxRecDepth 16384
set_option maxHeartbeats 1800000

theorem IndexedMemory.vector {α : Type*} {n : ℕ} (idx : α≃Fin n) (data : Vector (Fin n) n)
    (memory : ℕ→Bool) (base width : ℕ) :
    IndexedMemory.Represents idx (fun p => (data.get (idx p)).val) memory base width ↔
      BitArray.Represents memory base width (DoublingPass.words width data) := by
  constructor
  · intro h
    refine ⟨fun i => by simp,?_⟩
    intro i j hj
    have hh:=h (idx.symm i) j hj
    simpa [DoublingPass.words,IncidenceEncoding.words,Vector.get,Fin.cast] using hh
  · intro h p j hj
    have hh:=h.bits (idx p) j hj
    simpa [DoublingPass.words,IncidenceEncoding.words,Vector.get,Fin.cast] using hh

def StoredLabels (rows columns : ℕ) (target : Targets.Target rows columns)
    (memory : ℕ→Bool) (base width : ℕ) : Prop :=
  IndexedMemory.Represents (ColorData.index rows columns)
    (fun p => ((ColorData.labels rows columns target).get (ColorData.index rows columns p)).val)
    memory base width

theorem labels_vector (rows columns : ℕ) (target : Targets.Target rows columns)
    (memory : ℕ→Bool) (base width : ℕ) :
    StoredLabels rows columns target memory base width ↔
      BitArray.Represents memory base width (DoublingPass.words width (ColorData.labels rows columns target)) :=
  IndexedMemory.vector _ _ _ _ _

theorem assembled_labels (rows columns : ℕ) (target : Targets.Target rows (columns+1))
    (layout : ChildPermutation.Layout) (memory : ℕ→Bool)
    (h : BitArray.Represents memory layout.parentForward layout.parentWidth
      (ColorAssemble.finalOutput layout (ColorData.assembleData rows columns target))) :
    StoredLabels rows (columns+1) target memory layout.parentForward layout.parentWidth := by
  have vector : IndexedMemory.Represents (halfIndex (ColorData.index rows columns))
      (fun p => ((ColorData.assembleData rows columns target).values.get
        (halfIndex (ColorData.index rows columns) p)).val) memory layout.parentForward layout.parentWidth :=
    (IndexedMemory.vector _ _ _ _ _).mpr h
  have value (p : Columns (columns+1)×Fin (2^rows)) :
      ((ColorData.assembleData rows columns target).values.get (halfIndex (ColorData.index rows columns) p)).val=
        ((ColorData.labels rows (columns+1) target).get (ColorData.index rows (columns+1) p)).val := by
    simpa [ColorAssemble.Data.values,Vector.get,Fin.cast] using ColorData.assemble_value rows columns target p
  have changed:=(IndexedMemory.congr_value (halfIndex (ColorData.index rows columns)) _ _ value memory
    layout.parentForward layout.parentWidth).mp vector
  exact (IndexedMemory.congr_index (ColorData.index rows (columns+1))
    (halfIndex (ColorData.index rows columns)) (Storage.index_value_succ rows columns) _ memory
    layout.parentForward layout.parentWidth).mpr changed

#print axioms assembled_labels
end Maxwell.Cost.RoutingPorts.Complete.Tree
