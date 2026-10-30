import Maxwell.Continuum.SourceGeometryPacking

/-! Widths for the literal packed routing geometry are derived from the
verified source routes, including the count word at every path boundary. -/
noncomputable section
namespace Maxwell.Composition.SourceDecorationEnumeration
open Maxwell.Logical Maxwell.Logical.Routing Maxwell.Spectral.Lattice Maxwell.Cost
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192
variable (S : Source.SparseSystem) (precision : ℕ)

theorem shiftedPoint_embedding_bound (v : SourceRouting.Vertex S precision) (k : Fin 3) :
    shiftedPoint (SourceRouting.embedding S precision v) k≤(129*SourceRouting.side S precision:ℕ) := by
  have h := (Maxwell.Continuum.Parameters.sourceSite_coordinate S precision (.inl v) k).2
  rw [PhysicalParameters.routingSide_eq] at h
  change 2*SourceIncidence.position S precision v k≤(258*SourceRouting.side S precision:ℕ) at h
  rw [shiftedPoint_embedding]
  push_cast at h ⊢
  omega

theorem Represents.path_embedding {saved} (h : Represents S precision saved)
    (i : Fin ((sourceSquareEntries S precision).length+(sourceSquareEntries S precision).length))
    (x : Point) (hx : x∈saved.paths.get i) :
    ∃v:SourceRouting.Vertex S precision,x=SourceRouting.embedding S precision v := by
  let e := (SourceEnumeration.positiveEdgeEquiv S precision).symm i
  have he := h.path e
  rw [show SourceEnumeration.positiveEdgeEquiv S precision e=i from
    (SourceEnumeration.positiveEdgeEquiv S precision).apply_symm_apply i] at he
  rw [he,EdgeEmission.points,List.mem_map] at hx
  obtain ⟨j,hj,rfl⟩ := hx
  have hj' : j<(EdgeWalk.edgeWalk (SourceRouting.data S precision) e).length+1 := List.mem_range.mp hj
  refine ⟨Subdivision.edgeVertex (SourceRouting.data S precision) e ⟨j,hj'⟩,?_⟩
  simp only [SourceRouting.embedding,Subdivision.embedding_edgeVertex]

theorem Represents.path_length_bound {saved} (h : Represents S precision saved)
    (i : Fin ((sourceSquareEntries S precision).length+(sourceSquareEntries S precision).length)) :
    (saved.paths.get i).length≤1024*SourceRouting.side S precision+1 := by
  let e := (SourceEnumeration.positiveEdgeEquiv S precision).symm i
  have he := h.path e
  rw [show SourceEnumeration.positiveEdgeEquiv S precision e=i from
    (SourceEnumeration.positiveEdgeEquiv S precision).apply_symm_apply i] at he
  rw [he,EdgeEmission.points_length]
  exact Nat.add_le_add_right (SourceRouting.edge_length_le S precision e) 1

theorem pointWords_le (p : Point) (M : ℕ) (hp : ∀k,shiftedPoint p k≤(M:ℤ))
    (n : ℕ) (hn : n∈pointWords p) : n≤M := by
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  change p.1+4≤(M:ℤ) at h0
  change p.2.1+4≤(M:ℤ) at h1
  change p.2.2+16≤(M:ℤ) at h2
  simp only [pointWords,List.mem_cons,List.mem_nil_iff,or_false] at hn
  rcases hn with rfl|rfl|rfl <;> omega

theorem Represents.packed_member_bound {saved} (h : Represents S precision saved)
    (n : ℕ) (hn : n∈packed saved) : n≤1024*SourceRouting.side S precision+1 := by
  have hpoint (v : SourceRouting.Vertex S precision) (hn : n∈pointWords (SourceRouting.embedding S precision v)) :
      n≤1024*SourceRouting.side S precision+1 :=
    (pointWords_le _ _ (shiftedPoint_embedding_bound S precision v) n hn).trans (by omega)
  rw [packed,List.mem_append] at hn
  rcases hn with hn | hn
  · obtain ⟨x,hx,hn⟩ := List.mem_flatMap.mp hn
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    have he := h.original ((SourceEnumeration.vertexEquiv S precision).symm i)
    rw [(SourceEnumeration.vertexEquiv S precision).apply_symm_apply] at he
    rw [he] at hn
    exact hpoint _ hn
  · obtain ⟨i,_,hn⟩ := List.mem_flatMap.mp hn
    simp only [pathWords,List.mem_cons] at hn
    rcases hn with rfl|hn
    · exact Represents.path_length_bound S precision h i
    · obtain ⟨x,hx,hn⟩ := List.mem_flatMap.mp hn
      obtain ⟨v,rfl⟩ := Represents.path_embedding S precision h i x hx
      exact hpoint v hn

theorem Represents.packed_width {saved} (h : Represents S precision saved)
    (i : Fin (packedLength saved)) :
    ((packedVector saved).get i).bits.length≤(1024*SourceRouting.side S precision+1).bits.length := by
  have hmem : (packedVector saved).get i∈packed saved := by
    change (packed saved)[i.val]'(by rw [packed_length];exact i.isLt)∈packed saved
    exact List.getElem_mem _
  simpa only [Nat.size_eq_bits_len] using Nat.size_le_size
    (Represents.packed_member_bound S precision h _ hmem)

#print axioms Represents.packed_width
end Maxwell.Composition.SourceDecorationEnumeration
