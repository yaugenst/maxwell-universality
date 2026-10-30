import Maxwell.Continuum.StoredWellRecordIdentity

/-! All three emitted passes are exactly one indexed stream over the
proved duplicate-free chronological decorated-site enumeration. -/
namespace Maxwell.Continuum.WellOutput
open Maxwell.Cost Maxwell.Composition Maxwell.Composition.SourceDecorationEnumeration
open Maxwell.Logical.Routing Maxwell.Spectral.Lattice
set_option maxHeartbeats 6000000
set_option maxRecDepth 16384

def pathSites {v e : ℕ} (saved : SourceEmission.Geometry v e) (mediator : Bool) (i : Fin e) : List Site :=
  if mediator then (Segments.ofList (saved.paths.get i)).map mediatorPoint
  else (InternalSamples.ofList (saved.paths.get i)).map terminalPoint

def pathSitePrefix {v e : ℕ} (saved : SourceEmission.Geometry v e) (mediator : Bool) (count : ℕ) : List Site :=
  ((List.finRange e).take count).flatMap (pathSites saved mediator)

theorem pathSites_length {v e : ℕ} (saved : SourceEmission.Geometry v e) (mediator : Bool) (i : Fin e) :
    (pathSites saved mediator i).length=(saved.paths.get i).length-pathTrim mediator := by
  cases mediator <;> simp [pathSites,pathTrim]

theorem pathSitePrefix_length {v e : ℕ} (saved : SourceEmission.Geometry v e) (mediator : Bool) (count : ℕ) :
    (pathSitePrefix saved mediator count).length=pathPrefix saved (pathTrim mediator) count := by
  simp only [pathSitePrefix,List.length_flatMap,pathSites_length,pathPrefix]

theorem pathSitePrefix_succ {v e : ℕ} (saved : SourceEmission.Geometry v e) (mediator : Bool) (i : Fin e) :
    pathSitePrefix saved mediator (i.val+1)=pathSitePrefix saved mediator i.val++pathSites saved mediator i := by
  unfold pathSitePrefix
  rw [List.take_succ_eq_append_getElem (by simpa only [List.length_finRange] using i.isLt)]
  simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.getElem_finRange]
  rfl

theorem sites_split {v e : ℕ} (saved : SourceEmission.Geometry v e) :
    sites saved=(List.ofFn saved.original.get).map terminalPoint++pathSitePrefix saved false e++
      pathSitePrefix saved true e := by
  simp only [sites,terminalSamples,stepSamples,List.map_append,List.map_flatMap,pathSitePrefix,
    List.take_of_length_le (show (List.finRange e).length≤e by simp)]
  rfl

section
variable {v e : ℕ} (saved : SourceEmission.Geometry v e) (constants : ℕ→ℕ)
variable (B : Fin 3→ℕ) (L d t : ℕ) (hL : Even L)
variable (hshift : constants 982=L+L*t+8) (hscale : ∀j:Fin 3,constants (983+j.val)=2*L*d*B j)
variable (hword : constants 966=L)
variable (P : ℕ) (numerators : ℕ→ℤ) (profile template : List Bool)
variable (hp : ∀i:Fin e,∀x∈saved.paths.get i,∀j,0≤shiftedPoint x j)
include hL hshift hscale hword hp

 theorem pathChunk_eq (mediator : Bool) (first : ℕ) (i : Fin e) :
    pathChunk saved constants mediator P numerators profile template first i.val=
      IndexedRecordStream.bits (recordBits B L d t P numerators profile template)
        (pathSites saved mediator i) (first+pathPrefix saved (pathTrim mediator) i.val) := by
  simp only [pathChunk,pathLength,dite_eq_left i.isLt]
  cases mediator with
  | false =>
    exact internal_stream_eq saved constants B L d t hL hshift hscale hword P numerators profile template
      i (first+pathPrefix saved 2 i.val) (hp i)
  | true =>
    exact mediator_stream_eq saved constants B L d t hL hshift hscale hword P numerators profile template
      i (first+pathPrefix saved 1 i.val) (hp i)

 theorem pathsStream_eq (mediator : Bool) (first count : ℕ) (hcount : count≤e) :
    pathsStream saved constants mediator P numerators profile template first count=
      IndexedRecordStream.bits (recordBits B L d t P numerators profile template)
        (pathSitePrefix saved mediator count) first := by
  induction count with
  | zero => simp [pathsStream,pathSitePrefix,IndexedRecordStream.bits]
  | succ count ih =>
    let i : Fin e := ⟨count,by omega⟩
    have hstep := pathSitePrefix_succ saved mediator i
    change pathSitePrefix saved mediator (count+1)=_ at hstep
    rw [pathsStream_succ,ih (by omega),hstep,IndexedRecordStream.append,pathSitePrefix_length]
    exact congrArg (List.append _) (pathChunk_eq saved constants B L d t hL hshift hscale hword
      P numerators profile template hp mediator first i)

 theorem bodyBits_eq (hp0 : ∀i:Fin v,∀j,0≤shiftedPoint (saved.original.get i) j) :
    bodyBits saved constants P numerators profile template=
      IndexedRecordStream.bits (recordBits B L d t P numerators profile template) (sites saved) 0 := by
  rw [bodyBits,originals_stream_eq saved constants B L d t hL hshift hscale hword P numerators profile template 0 hp0,
    pathsStream_eq saved constants B L d t hL hshift hscale hword P numerators profile template hp false v e le_rfl,
    pathsStream_eq saved constants B L d t hL hshift hscale hword P numerators profile template hp true
      (v+pathPrefix saved 2 e) e le_rfl,
    sites_split,IndexedRecordStream.append,IndexedRecordStream.append]
  simp only [List.length_append,List.length_map,List.length_ofFn,pathSitePrefix_length,pathTrim,
    Bool.false_eq_true,ite_false,Nat.zero_add]

 theorem bits_eq (hp0 : ∀i:Fin v,∀j,0≤shiftedPoint (saved.original.get i) j) :
    bits saved constants P numerators profile template=Codec.nat (sites saved).length++
      IndexedRecordStream.bits (recordBits B L d t P numerators profile template) (sites saved) 0 := by
  rw [bits,sites_length,bodyBits_eq saved constants B L d t hL hshift hscale hword P numerators profile template hp hp0]

end
#print axioms bodyBits_eq
#print axioms bits_eq
end Maxwell.Continuum.WellOutput
