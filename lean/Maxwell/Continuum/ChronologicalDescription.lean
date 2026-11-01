import Maxwell.Continuum.ChronologicalWellEncoding
import Maxwell.Continuum.ContinuumDescription

/-! The executable representation orders wells by the stored routing walk.
This is the same physical record family and has exactly the old bit length. -/

noncomputable section
namespace Maxwell.Continuum.RealizationParameters

variable (p : Source.Parameters) (S : Source.SparseSystem) (hm : 0<S.nnz)

def chronologicalDescriptionBits (j : Fin (drawCount p S hm)) : List Bool :=
  headerBits p S hm j++ambientBits p S hm++chronologicalWellStream p S hm++
    sourceStream p S hm++readoutPlacementStream p S hm

theorem chronologicalWellStream_same_length :
    (chronologicalWellStream p S hm).length=(wellStream p S hm).length := by
  have h := chronological_well_records_perm p S hm
  have hs := (h.map List.length).sum_eq
  simp only [chronologicalWellStream,wellStream,Codec.list,List.length_append,
    List.length_flatMap]
  have hn := (chronological_vertices_perm p S hm).length_eq
  rw [hn]
  simpa only [List.map_map,Function.comp_def] using congrArg
    (fun n => (Codec.nat (Finset.univ : Finset (Maxwell.Composition.SourceDecoration.Vertex S
      (precision p S hm))).toList.length).length+n) hs

theorem chronologicalDescriptionBits_length (j : Fin (drawCount p S hm)) :
    (chronologicalDescriptionBits p S hm j).length=(descriptionBits p S hm j).length := by
  simp only [chronologicalDescriptionBits,descriptionBits,List.length_append,
    chronologicalWellStream_same_length]

#print axioms chronologicalDescriptionBits_length

end Maxwell.Continuum.RealizationParameters
