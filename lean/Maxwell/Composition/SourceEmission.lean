import Maxwell.Composition.SourceRouting
import Maxwell.Composition.PositiveScatter
import Maxwell.Logical.Routing.Transport

/-! The finite output of the logical geometric compiler. Original vertices,
coefficients and active paths are stored in arrays; every path shares one
routing schedule and placement history. -/

namespace Maxwell.Composition.SourceEmission
open Maxwell.Logical
open Maxwell.Logical.Routing
open Maxwell.Logical.Routing.Gluing
open Maxwell.Logical.Routing.EdgeEmission

structure Geometry (vertices edges : ℕ) where
  original : Vector Point vertices
  diagonal : Vector ℚ vertices
  paths : Vector (List Point) edges

/-- Finite source-derived geometry, with preparation outside the edge loop. -/
def geometry (S : Source.SparseSystem) (precision : ℕ) :
    Geometry ((sourceCircuit S precision).size + (sourceCircuit S precision).size +
      (sourceSquareEntries S precision).length)
      ((sourceSquareEntries S precision).length + (sourceSquareEntries S precision).length) :=
  let data := SourceRouting.indexedData S precision
  let saved := prepare data
  { original := Vector.ofFn (vertexPoint data)
    diagonal := PositiveScatter.diagonal S precision
    paths := Vector.ofFn (edge data saved) }

theorem cast_half_edge {V E : Type*} {a b : ℕ} (h : a = b) (data : Data V E a) (e : E) :
    edge (SourceRouting.castDataHalf h data) (prepare (SourceRouting.castDataHalf h data)) e =
      edge data (prepare data) e := by
  subst b
  rfl

theorem cast_half_vertexPoint {V E : Type*} {a b : ℕ} (h : a = b)
    (data : Data V E a) (v : V) :
    vertexPoint (SourceRouting.castDataHalf h data) v = vertexPoint data v := by
  subst b
  rfl

theorem original_eq (S : Source.SparseSystem) (precision : ℕ)
    (v : SourcePositive.Vertex S precision) :
    (geometry S precision).original.get (SourceEnumeration.vertexEquiv S precision v) =
      SourceRouting.embedding S precision (.inl v) := by
  simp only [geometry, SortArrays.get_ofFn, SourceRouting.embedding, Subdivision.embedding,
    SourceRouting.data, cast_half_vertexPoint, transport_vertexPoint]

theorem diagonal_eq (S : Source.SparseSystem) (precision : ℕ)
    (v : SourcePositive.Vertex S precision) :
    ((geometry S precision).diagonal.get (SourceEnumeration.vertexEquiv S precision v) : ℝ) =
      PositiveEdges.diagonal (SourcePositive.sourceH S precision) v :=
  PositiveScatter.diagonal_cast S precision v

/-- The array-backed compiler output is exactly the semantic path sequence. -/
theorem path_eq (S : Source.SparseSystem) (precision : ℕ)
    (e : SourceRouting.Edge S precision) :
    (geometry S precision).paths.get (SourceEnumeration.positiveEdgeEquiv S precision e) =
      points (EdgeWalk.edgeWalk (SourceRouting.data S precision) e) := by
  rw [← edge_eq]
  simp only [SourceRouting.data, cast_half_edge, transport_edge, geometry, SortArrays.get_ofFn]

theorem path_length (S : Source.SparseSystem) (precision : ℕ)
    (e : SourceRouting.Edge S precision) :
    ((geometry S precision).paths.get (SourceEnumeration.positiveEdgeEquiv S precision e)).length =
      (EdgeWalk.edgeWalk (SourceRouting.data S precision) e).length + 1 := by
  rw [path_eq, points_length]

/-- Every emitted path sample is the same selected vertex used by Γ. -/
theorem path_sample (S : Source.SparseSystem) (precision : ℕ)
    (e : SourceRouting.Edge S precision)
    (t : Fin ((EdgeWalk.edgeWalk (SourceRouting.data S precision) e).length + 1)) :
    ((geometry S precision).paths.get (SourceEnumeration.positiveEdgeEquiv S precision e))[t.val]'
        (by rw [path_length]; exact t.isLt) =
      SourceRouting.embedding S precision (Subdivision.edgeVertex (SourceRouting.data S precision) e t) := by
  simp only [path_eq, points, List.getElem_map, List.getElem_range,
    SourceRouting.embedding, Subdivision.embedding_edgeVertex]

theorem path_length_le (S : Source.SparseSystem) (precision : ℕ)
    (e : Fin ((sourceSquareEntries S precision).length + (sourceSquareEntries S precision).length)) :
    ((geometry S precision).paths.get e).length ≤
      1024 * (2 * portHalfSide ((sourceCircuit S precision).size + (sourceCircuit S precision).size +
        (sourceSquareEntries S precision).length)) + 1 := by
  simpa only [geometry, SortArrays.get_ofFn] using edge_length_le (SourceRouting.indexedData S precision) e

end Maxwell.Composition.SourceEmission
