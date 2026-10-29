import Maxwell.Logical.Routing.IndexedData
import Maxwell.Logical.Routing.EdgeEmission

/-! Relabeling graph identifiers preserves the literal cached path output. -/

namespace Maxwell.Logical.Routing.Gluing
open EdgeEmission

@[simp] theorem transport_vertexPoint {V E W F : Type*} {half : ℕ}
    (vertex : V ≃ W) (edge : E ≃ F) (data : Data W F half) (v : V) :
    vertexPoint (transportData vertex edge data) v = vertexPoint data (vertex v) := rfl

@[simp] theorem transport_token {V E W F : Type*} {half : ℕ}
    (vertex : V ≃ W) (edge : E ≃ F) (data : Data W F half) (e : E) (b : Bool) :
    token (transportData vertex edge data) (e, b) = token data (edge e, b) := by
  simp only [token, transportData, Equiv.apply_symm_apply]

theorem transport_bottomPrefix {V E W F : Type*} {half : ℕ}
    (vertex : V ≃ W) (edge : E ≃ F) (data : Data W F half) (e : E) (b : Bool) :
    bottomPrefix (transportData vertex edge data) (e, b) = bottomPrefix data (edge e, b) := by
  simp only [bottomPrefix, transportData, tileTranslation, Equiv.apply_symm_apply]

theorem transport_edge {V E W F : Type*} {half : ℕ}
    (vertex : V ≃ W) (edges : E ≃ F) (data : Data W F half) (e : E) :
    edge (transportData vertex edges data) (prepare (transportData vertex edges data)) e =
      edge data (prepare data) (edges e) := by
  simp only [edge, legPoints, transport_bottomPrefix, transport_token]
  rfl

theorem transport_edge_points {V E W F : Type*} {half : ℕ}
    (vertex : V ≃ W) (edges : E ≃ F) (data : Data W F half) (e : E) :
    points (EdgeWalk.edgeWalk (transportData vertex edges data) e) =
      points (EdgeWalk.edgeWalk data (edges e)) := by
  rw [← edge_eq, ← edge_eq, transport_edge]

end Maxwell.Logical.Routing.Gluing
