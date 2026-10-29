import Maxwell.Composition.SourceVertexList
import Maxwell.Composition.SourceEdgeBounds
import Maxwell.Composition.SourceDecoration

/-! Actual emitted list lengths match the semantic dimensions used by the
spectral proof. Enumerations themselves remain the sparse constructors. -/
noncomputable section
namespace Maxwell.Composition.SourceRecordCounts

private theorem complete_length {α : Type*} [Fintype α] [DecidableEq α]
    (xs : List α) (h : xs.Nodup) (hc : ∀ a, a ∈ xs) : xs.length = Fintype.card α := by
  have he : xs.toFinset = Finset.univ := by ext a; simp only [List.mem_toFinset, Finset.mem_univ, iff_true]; exact hc a
  rw [← List.toFinset_card_of_nodup h, he, Finset.card_univ]

theorem vertices_length (S : Source.SparseSystem) (precision : ℕ) :
    (SourceVertexList.entries S precision).length = Fintype.card (SourceRouting.Vertex S precision) := by
  classical
  rw [SourceVertexList.entries_eq, List.length_map]
  exact complete_length _ (SourceVertexList.vertexList_nodup S precision)
    (SourceVertexList.vertexList_complete S precision)

theorem edges_length (S : Source.SparseSystem) (precision : ℕ) :
    (SourceEdgeList.edges S precision).length = Fintype.card (SourceIncidence.E S precision) := by
  classical
  have hn := (SourceSegmentList.stepList_nodup S precision).map
    (SourceEdgeEnumeration.toEdge_injective S precision)
  have hc (e : SourceIncidence.E S precision) : e ∈
      (SourceSegmentList.stepList S precision).map (SourceEdgeEnumeration.toEdge S precision) := by
    obtain ⟨s, rfl⟩ := SourceEdgeEnumeration.toEdge_surjective S precision e
    exact List.mem_map.mpr ⟨s, SourceSegmentList.stepList_complete S precision s, rfl⟩
  have hl := complete_length _ hn hc
  rw [List.length_map] at hl
  rw [SourceEdgeList.edges_eq, List.length_map]
  exact hl

theorem defects_length (S : Source.SparseSystem) (precision : ℕ) :
    (SourceVertexList.entries S precision).length + (SourceEdgeList.edges S precision).length =
      Fintype.card (SourceDecoration.Vertex S precision) := by
  rw [vertices_length, edges_length]
  exact Fintype.card_sum.symm

theorem vertices_length_le_box (S : Source.SparseSystem) (precision : ℕ) :
    (SourceVertexList.entries S precision).length ≤
      Logical.Routing.boxSites (SourceRouting.side S precision) := by
  rw [vertices_length]
  exact SourceRouting.vertex_card_le_box S precision

end Maxwell.Composition.SourceRecordCounts
