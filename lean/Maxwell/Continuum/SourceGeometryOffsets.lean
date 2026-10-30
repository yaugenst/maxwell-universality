import Maxwell.Continuum.SourceGeometryLookup
import Maxwell.Continuum.SourceGeometryPackingBounds

/-! Exact span and successor equations for the runtime path cursor. -/
namespace Maxwell.Composition.SourceDecorationEnumeration
open Maxwell.Logical Maxwell.Logical.Routing Maxwell.Spectral.Lattice Maxwell.Cost
set_option maxHeartbeats 2200000
set_option maxRecDepth 16384

theorem pathOffset_zero {v e : ℕ} (saved : SourceEmission.Geometry v e) : pathOffset saved 0=3*v := by
  simp [pathOffset]

theorem pathOffset_succ {v e : ℕ} (saved : SourceEmission.Geometry v e) (i : Fin e) :
    pathOffset saved (i.val+1)=pathOffset saved i.val+1+3*(saved.paths.get i).length := by
  unfold pathOffset
  rw [List.take_succ_eq_append_getElem (by simpa only [List.length_finRange] using i.isLt)]
  simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    List.length_append,List.getElem_finRange,pathWords_length]
  simp only [Nat.add_assoc]
  rfl

theorem pathOffset_end {v e : ℕ} (saved : SourceEmission.Geometry v e) :
    pathOffset saved e=packedLength saved := by
  rw [←packed_length]
  simp only [pathOffset,packed,List.length_append,triples_length,List.length_ofFn,
    List.take_of_length_le (show (List.finRange e).length≤e by simp)]

theorem pathOffset_span {v e : ℕ} (saved : SourceEmission.Geometry v e) (i : Fin e) :
    pathOffset saved i.val+1+3*(saved.paths.get i).length≤packedLength saved := by
  have he := congrArg List.length (path_decomposition saved i)
  simp only [packed_length,List.length_append,triples_length,List.length_ofFn,pathWords_length] at he
  unfold pathOffset
  omega

theorem originals_span {v e : ℕ} (saved : SourceEmission.Geometry v e) : 3*v≤packedLength saved := by
  unfold packedLength
  omega

noncomputable section
variable (S : Source.SparseSystem) (precision : ℕ)

theorem Represents.path_length_two {saved} (h : Represents S precision saved)
    (i : Fin ((sourceSquareEntries S precision).length+(sourceSquareEntries S precision).length)) :
    2≤(saved.paths.get i).length := by
  let e := (SourceEnumeration.positiveEdgeEquiv S precision).symm i
  have he := h.path e
  rw [show SourceEnumeration.positiveEdgeEquiv S precision e=i from
    (SourceEnumeration.positiveEdgeEquiv S precision).apply_symm_apply i] at he
  rw [he,EdgeEmission.points_length]
  obtain ⟨j,hj⟩ := EdgeWalk.edgeWalk_wire_form (SourceRouting.data S precision) e
  omega

#print axioms pathOffset_span
#print axioms Represents.path_length_two
end
end Maxwell.Composition.SourceDecorationEnumeration
