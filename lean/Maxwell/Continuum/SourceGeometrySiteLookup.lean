import Maxwell.Continuum.SourceGeometryPathCounts
import Maxwell.Cost.ListBlocks

/-! Exact indices of original, internal, and adjacent-pair sites in the
chronological physical-well list. -/
namespace Maxwell.Composition.SourceDecorationEnumeration
open Maxwell.Logical.Routing Maxwell.Spectral.Lattice
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def internalSites {v e : ℕ} (saved : SourceEmission.Geometry v e) : List Site :=
  (List.finRange e).flatMap (fun i=>(InternalSamples.ofList (saved.paths.get i)).map terminalPoint)

def mediatorSites {v e : ℕ} (saved : SourceEmission.Geometry v e) : List Site :=
  (List.finRange e).flatMap (fun i=>(Segments.ofList (saved.paths.get i)).map mediatorPoint)

theorem sites_blocks {v e : ℕ} (saved : SourceEmission.Geometry v e) :
    sites saved=(List.ofFn saved.original.get).map terminalPoint++internalSites saved++mediatorSites saved := by
  simp only [sites,terminalSamples,stepSamples,List.map_append,List.map_flatMap,internalSites,mediatorSites]

theorem internalSites_length {v e : ℕ} (saved : SourceEmission.Geometry v e) :
    (internalSites saved).length=pathPrefix saved 2 e := by
  simp only [internalSites,List.length_flatMap,List.length_map,InternalSamples.length,pathPrefix_end]

theorem mediatorSites_length {v e : ℕ} (saved : SourceEmission.Geometry v e) :
    (mediatorSites saved).length=pathPrefix saved 1 e := by
  simp only [mediatorSites,List.length_flatMap,List.length_map,Segments.length,pathPrefix_end]

theorem original_site_lookup {v e : ℕ} (saved : SourceEmission.Geometry v e) (i : Fin v) :
    (sites saved)[i.val]?=some (terminalPoint (saved.original.get i)) := by
  rw [sites_blocks,List.append_assoc,List.getElem?_append_left (by simpa only [List.length_map,List.length_ofFn] using i.isLt)]
  simp only [List.getElem?_map,List.getElem?_ofFn,dite_eq_left i.isLt,Option.map_some]

theorem internal_site_lookup {v e : ℕ} (saved : SourceEmission.Geometry v e) (i : Fin e)
    (j : ℕ) (hj : j<(saved.paths.get i).length-2) :
    (sites saved)[v+pathPrefix saved 2 i.val+j]?=
      some (terminalPoint ((saved.paths.get i)[j+1]'(by omega))) := by
  let f : Fin e→List Site := fun k=>(InternalSamples.ofList (saved.paths.get k)).map terminalPoint
  have blockLookup := Maxwell.ListBlocks.getElem?_finRange f i j (by
    simp only [f,List.length_map,InternalSamples.length];exact hj)
  simp only [f,List.length_map,InternalSamples.length] at blockLookup
  have local' : (internalSites saved)[pathPrefix saved 2 i.val+j]?=
      some (terminalPoint ((saved.paths.get i)[j+1]'(by omega))) := by
    simpa only [internalSites,pathPrefix,InternalSamples.ofList,List.getElem_map,
      List.getElem_dropLast,List.getElem_tail] using blockLookup
  have bound := (List.getElem?_eq_some_iff.mp local').choose
  rw [sites_blocks,List.append_assoc,
    show v+pathPrefix saved 2 i.val+j=((List.ofFn saved.original.get).map terminalPoint).length+
      (pathPrefix saved 2 i.val+j) by simp only [List.length_map,List.length_ofFn];omega,
    List.getElem?_append_right (Nat.le_add_right _ _),Nat.add_sub_cancel_left,List.getElem?_append_left bound]
  exact local'

theorem mediator_site_lookup {v e : ℕ} (saved : SourceEmission.Geometry v e) (i : Fin e)
    (j : ℕ) (hj : j<(saved.paths.get i).length-1) :
    (sites saved)[v+pathPrefix saved 2 e+pathPrefix saved 1 i.val+j]?=
      some (mediatorPoint (((saved.paths.get i)[j]'(by omega)),((saved.paths.get i)[j+1]'(by omega)))) := by
  let f : Fin e→List Site := fun k=>(Segments.ofList (saved.paths.get k)).map mediatorPoint
  have blockLookup := Maxwell.ListBlocks.getElem?_finRange f i j (by
    simp only [f,List.length_map,Segments.length];exact hj)
  simp only [f,List.length_map,Segments.length] at blockLookup
  have local' : (mediatorSites saved)[pathPrefix saved 1 i.val+j]?=
      some (mediatorPoint (((saved.paths.get i)[j]'(by omega)),((saved.paths.get i)[j+1]'(by omega)))) := by
    simpa only [mediatorSites,pathPrefix,Segments.ofList,List.getElem_map,List.getElem_zip,
      List.getElem_tail] using blockLookup
  rw [sites_blocks,show v+pathPrefix saved 2 e+pathPrefix saved 1 i.val+j=
      (((List.ofFn saved.original.get).map terminalPoint)++internalSites saved).length+
        (pathPrefix saved 1 i.val+j) by
      simp only [List.length_append,List.length_map,List.length_ofFn,internalSites_length];omega,
    List.getElem?_append_right (Nat.le_add_right _ _),Nat.add_sub_cancel_left]
  exact local'

#print axioms internal_site_lookup
#print axioms mediator_site_lookup
end Maxwell.Composition.SourceDecorationEnumeration
