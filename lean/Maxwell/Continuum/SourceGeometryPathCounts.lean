import Maxwell.Continuum.SourceGeometryOffsets

/-! Exact prefix counts for the chronological vertex and edge passes. -/
namespace Maxwell.Composition.SourceDecorationEnumeration
open Maxwell.Logical Maxwell.Logical.Routing Maxwell.Spectral.Lattice Maxwell.Cost
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

def pathPrefix {v e : ℕ} (saved : SourceEmission.Geometry v e) (trim i : ℕ) : ℕ :=
  (((List.finRange e).take i).map (fun a=>(saved.paths.get a).length-trim)).sum

theorem pathPrefix_zero {v e : ℕ} (saved : SourceEmission.Geometry v e) (trim : ℕ) :
    pathPrefix saved trim 0=0 := by simp [pathPrefix]

theorem pathPrefix_succ {v e : ℕ} (saved : SourceEmission.Geometry v e) (trim : ℕ) (i : Fin e) :
    pathPrefix saved trim (i.val+1)=pathPrefix saved trim i.val+((saved.paths.get i).length-trim) := by
  unfold pathPrefix
  rw [List.take_succ_eq_append_getElem (by simpa only [List.length_finRange] using i.isLt)]
  simp only [List.map_append,List.map_cons,List.map_nil,List.sum_append,List.sum_cons,
    List.sum_nil,Nat.add_zero,List.getElem_finRange]
  rfl

theorem pathPrefix_end {v e : ℕ} (saved : SourceEmission.Geometry v e) (trim : ℕ) :
    pathPrefix saved trim e=((List.finRange e).map (fun i=>(saved.paths.get i).length-trim)).sum := by
  simp only [pathPrefix,List.take_of_length_le (show (List.finRange e).length≤e by simp)]

theorem pathPrefix_le_end {v e : ℕ} (saved : SourceEmission.Geometry v e) (trim i : ℕ) :
    pathPrefix saved trim i≤pathPrefix saved trim e := by
  have h := congrArg (fun xs : List (Fin e)=>(xs.map (fun a=>(saved.paths.get a).length-trim)).sum)
    (List.take_append_drop i (List.finRange e))
  simp only [List.map_append,List.sum_append] at h
  rw [pathPrefix_end]
  unfold pathPrefix
  omega

theorem siteCount_eq_prefix {v e : ℕ} (saved : SourceEmission.Geometry v e) :
    siteCount saved=v+pathPrefix saved 2 e+pathPrefix saved 1 e := by
  rw [pathPrefix_end,pathPrefix_end]
  rfl

#print axioms pathPrefix_succ
#print axioms siteCount_eq_prefix
end Maxwell.Composition.SourceDecorationEnumeration
