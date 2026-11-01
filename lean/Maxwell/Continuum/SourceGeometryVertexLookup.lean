import Maxwell.Continuum.SourceGeometrySiteLookup

/-! Physical vertex identities at the actual chronological traversal indices.
The saved geometry contract is sufficient; no runtime trace is assumed. -/
noncomputable section
namespace Maxwell.Composition.SourceDecorationEnumeration
open Maxwell.Logical Maxwell.Logical.Routing Maxwell.Spectral.Lattice
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384
variable (S : Source.SparseSystem) (precision : ℕ)

theorem Represents.vertex_lookup {saved} (h : Represents S precision saved)
    (index : ℕ) (vertex : SourceDecoration.Vertex S precision)
    (atSite : (sites saved)[index]?=some (SourceDecoration.site S precision vertex)) :
    (vertexList S precision)[index]?=some vertex := by
  rw [h.sites_eq,List.getElem?_map] at atSite
  cases atVertex : (vertexList S precision)[index]? with
  | none => simp only [atVertex,Option.map_none] at atSite; cases atSite
  | some actual =>
    rw [atVertex,Option.map_some] at atSite
    have he := SourceDecoration.site_injective S precision (Option.some.inj atSite)
    simp only [he]

theorem Represents.path_points {saved} (h : Represents S precision saved)
    (i : Fin ((sourceSquareEntries S precision).length+(sourceSquareEntries S precision).length)) :
    saved.paths.get i=EdgeEmission.points (EdgeWalk.edgeWalk (SourceRouting.data S precision)
      ((SourceEnumeration.positiveEdgeEquiv S precision).symm i)) := by
  simpa only [Equiv.apply_symm_apply] using
    h.path ((SourceEnumeration.positiveEdgeEquiv S precision).symm i)

theorem Represents.path_length {saved} (h : Represents S precision saved)
    (i : Fin ((sourceSquareEntries S precision).length+(sourceSquareEntries S precision).length)) :
    (saved.paths.get i).length=(EdgeWalk.edgeWalk (SourceRouting.data S precision)
      ((SourceEnumeration.positiveEdgeEquiv S precision).symm i)).length+1 := by
  rw [h.path_points]
  simp only [EdgeEmission.points,List.length_map,List.length_range]

theorem Represents.path_point {saved} (h : Represents S precision saved)
    (i : Fin ((sourceSquareEntries S precision).length+(sourceSquareEntries S precision).length))
    (j : ℕ) (hj : j<(saved.paths.get i).length) :
    (saved.paths.get i)[j]=(EdgeWalk.edgeWalk (SourceRouting.data S precision)
      ((SourceEnumeration.positiveEdgeEquiv S precision).symm i)).point j := by
  simp only [h.path_points,EdgeEmission.points,List.getElem_map,List.getElem_range]

theorem Represents.original_vertex_lookup {saved} (h : Represents S precision saved)
    (i : Fin ((sourceCircuit S precision).size+(sourceCircuit S precision).size+
      (sourceSquareEntries S precision).length)) :
    (vertexList S precision)[i.val]?=
      some (.inl (.inl ((SourceEnumeration.vertexEquiv S precision).symm i))) := by
  apply h.vertex_lookup
  have he := h.original ((SourceEnumeration.vertexEquiv S precision).symm i)
  rw [Equiv.apply_symm_apply] at he
  rw [original_site_lookup,he]
  exact congrArg some (terminalPoint_embedding S precision
    (.inl ((SourceEnumeration.vertexEquiv S precision).symm i)))

theorem Represents.internal_vertex_lookup {saved} (h : Represents S precision saved)
    (i : Fin ((sourceSquareEntries S precision).length+(sourceSquareEntries S precision).length))
    (t : Fin ((EdgeWalk.edgeWalk (SourceRouting.data S precision)
      ((SourceEnumeration.positiveEdgeEquiv S precision).symm i)).length-1)) :
    (vertexList S precision)[(sourceCircuit S precision).size+(sourceCircuit S precision).size+
      (sourceSquareEntries S precision).length+pathPrefix saved 2 i.val+t.val]?=
      some (.inl (.inr ⟨(SourceEnumeration.positiveEdgeEquiv S precision).symm i,t⟩)) := by
  apply h.vertex_lookup
  have ht : t.val<(saved.paths.get i).length-2 := by rw [h.path_length];omega
  rw [internal_site_lookup saved i t.val ht,h.path_point]
  exact congrArg some (terminalPoint_embedding S precision
    (.inr ⟨(SourceEnumeration.positiveEdgeEquiv S precision).symm i,t⟩))

theorem Represents.mediator_vertex_lookup {saved} (h : Represents S precision saved)
    (i : Fin ((sourceSquareEntries S precision).length+(sourceSquareEntries S precision).length))
    (t : Fin (EdgeWalk.edgeWalk (SourceRouting.data S precision)
      ((SourceEnumeration.positiveEdgeEquiv S precision).symm i)).length) :
    (vertexList S precision)[(sourceCircuit S precision).size+(sourceCircuit S precision).size+
      (sourceSquareEntries S precision).length+
      pathPrefix saved 2 ((sourceSquareEntries S precision).length+(sourceSquareEntries S precision).length)+
      pathPrefix saved 1 i.val+t.val]?=
      some (.inr (SourceEdgeEnumeration.toEdge S precision
        ⟨(SourceEnumeration.positiveEdgeEquiv S precision).symm i,t⟩)) := by
  apply h.vertex_lookup
  have ht : t.val<(saved.paths.get i).length-1 := by rw [h.path_length];omega
  rw [mediator_site_lookup saved i t.val ht,h.path_point,h.path_point]
  rw [←SourceSegmentList.pair_apply]
  exact congrArg some (mediatorPoint_pair S precision
    ⟨(SourceEnumeration.positiveEdgeEquiv S precision).symm i,t⟩)

#print axioms Represents.original_vertex_lookup
#print axioms Represents.internal_vertex_lookup
#print axioms Represents.mediator_vertex_lookup
end Maxwell.Composition.SourceDecorationEnumeration
