import Maxwell.Continuum.SubdivisionOriginalCounts

/-! The finite strength formulas use exactly the degree of the routed
physical graph: two internally and the original saved incidence count at
original vertices. No adjacency matrix is scanned by the encoder. -/
noncomputable section
namespace Maxwell.Composition.PhysicalDiagonal
open Maxwell.Logical.Routing
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3500000
set_option maxRecDepth 8192
variable (S : Source.SparseSystem) (precision : ℕ)

 theorem degree_eq_steps (v : SourceIncidence.V S precision) :
    degree S precision v=(SubdivisionSteps.incidentSteps (SourceRouting.data S precision) v).card := by
  let e := SourceEdgeEnumeration.equiv S precision
  have he := e.subtypeEquiv
    (p := fun s=>v=SourceSteps.left S precision s ∨ v=SourceSteps.right S precision s)
    (q := fun f : SourceIncidence.E S precision=>v=f.val.1 ∨ v=f.val.2) (by
      intro s
      rcases SourceEdgeEnumeration.toEdge_endpoints S precision s with h | h
      · change (v=SourceSteps.left S precision s ∨ v=SourceSteps.right S precision s) ↔
          v=(SourceEdgeEnumeration.toEdge S precision s).val.1 ∨
          v=(SourceEdgeEnumeration.toEdge S precision s).val.2
        rw [h.1,h.2]
      · change (v=SourceSteps.left S precision s ∨ v=SourceSteps.right S precision s) ↔
          v=(SourceEdgeEnumeration.toEdge S precision s).val.1 ∨
          v=(SourceEdgeEnumeration.toEdge S precision s).val.2
        rw [h.1,h.2,or_comm])
  have hc := Fintype.card_congr he
  calc
    degree S precision v = Fintype.card {f : SourceIncidence.E S precision // v=f.val.1 ∨ v=f.val.2} :=
      (Fintype.card_subtype _).symm
    _ = Fintype.card {s : SourceSteps.Step S precision //
        v=SourceSteps.left S precision s ∨ v=SourceSteps.right S precision s} := hc.symm
    _ = _ := Fintype.card_subtype _

theorem degree_internal (e : SourceRouting.Edge S precision)
    (i : Fin ((EdgeWalk.edgeWalk (SourceRouting.data S precision) e).length-1)) :
    degree S precision (.inr ⟨e,i⟩)=2 := by
  erw [degree_eq_steps]
  exact SubdivisionSteps.incidentSteps_internal_card _ e i

theorem degree_original (v : SourcePositive.Vertex S precision) :
    degree S precision (.inl v)=
      (Finset.univ.filter (fun p : SourceRouting.Edge S precision×Bool=>
        (SourcePositive.graph S precision).endpoint p.1 p.2=v)).card := by
  erw [degree_eq_steps,SubdivisionSteps.incidentSteps_original_card]
  congr 1
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  rw [SourceRouting.data_endpoint]

theorem diagonal_internal (α : ℚ) (β : Maxwell.Spectral.Lattice.Direction→ℚ)
    (e : SourceRouting.Edge S precision)
    (i : Fin ((EdgeWalk.edgeWalk (SourceRouting.data S precision) e).length-1)) :
    diagonal S precision α β (.inl (.inr ⟨e,i⟩))= -2*α := by
  change α*(0-(degree S precision (.inr ⟨e,i⟩):ℚ))= -2*α
  erw [degree_internal]
  norm_num
  ring

#print axioms degree_internal
#print axioms degree_original
end Maxwell.Composition.PhysicalDiagonal
