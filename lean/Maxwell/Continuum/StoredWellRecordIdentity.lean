import Maxwell.Continuum.StoredWellStream
import Maxwell.Continuum.IndexedRecordStream

/-! Identification of the emitted complete records with the actual
chronological lattice sites, including the physical placement formula. -/
namespace Maxwell.Continuum.WellOutput
open Maxwell.Cost Maxwell.Composition Maxwell.Composition.SourceDecorationEnumeration
open Maxwell.Logical.Routing Maxwell.Spectral.Lattice
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def centerBits (B : Fin 3→ℕ) (L d t : ℕ) (x : Site) : List Bool :=
  Codec.int (centerPoint (fun j=>(B j:ℤ)) L d t x 0)++
  Codec.int (centerPoint (fun j=>(B j:ℤ)) L d t x 1)++
  Codec.int (centerPoint (fun j=>(B j:ℤ)) L d t x 2)++Codec.nat L

def recordBits (B : Fin 3→ℕ) (L d t P : ℕ) (numerators : ℕ→ℤ)
    (profile template : List Bool) (i : ℕ) (x : Site) : List Bool :=
  centerBits B L d t x++WellPayload.bits P (numerators i) profile template

theorem internalSamples_ofFn {α : Type*} (xs : List α) :
    InternalSamples.ofList xs=List.ofFn (fun i:Fin (xs.length-2)=>xs[i.val+1]'(by omega)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [InternalSamples.ofList,List.getElem_dropLast,List.getElem_tail,List.getElem_ofFn]

theorem stepSamples_ofFn {α : Type*} (xs : List α) :
    Segments.ofList xs=List.ofFn (fun i:Fin (xs.length-1)=>
      (xs[i.val]'(by omega),xs[i.val+1]'(by omega))) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [Segments.ofList,List.getElem_zip,List.getElem_tail,List.getElem_ofFn]

section
variable {v e : ℕ} (saved : SourceEmission.Geometry v e) (constants : ℕ→ℕ)
variable (B : Fin 3→ℕ) (L d t : ℕ) (hL : Even L)
variable (hshift : constants 982=L+L*t+8) (hscale : ∀j:Fin 3,constants (983+j.val)=2*L*d*B j)
variable (hword : constants 966=L)
variable (P : ℕ) (numerators : ℕ→ℤ) (profile template : List Bool)
include hL hshift hscale hword

 theorem originals_stream_eq (first : ℕ)
    (hp : ∀i:Fin v,∀j,0≤shiftedPoint (saved.original.get i) j) :
    terminalStream (packedVector saved) constants P numerators profile template 0 first v=
      IndexedRecordStream.bits (recordBits B L d t P numerators profile template)
        ((List.ofFn saved.original.get).map terminalPoint) first := by
  rw [IndexedRecordStream.map,IndexedRecordStream.ofFn]
  unfold terminalStream
  rw [←List.map_coe_finRange_eq_range,List.flatMap_map]
  apply List.flatMap_congr
  intro i _
  simp only [Nat.zero_add,recordBits]
  congr 1
  unfold GeometryOutput.terminalBits centerBits
  rw [hword,original_record_coordinate saved constants B L d t hL hshift hscale i (hp i) 0,
    original_record_coordinate saved constants B L d t hL hshift hscale i (hp i) 1,
    original_record_coordinate saved constants B L d t hL hshift hscale i (hp i) 2]

 theorem internal_stream_eq (i : Fin e) (first : ℕ)
    (hp : ∀x∈saved.paths.get i,∀j,0≤shiftedPoint x j) :
    terminalStream (packedVector saved) constants P numerators profile template
        (pathOffset saved i.val+4) first ((saved.paths.get i).length-2)=
      IndexedRecordStream.bits (recordBits B L d t P numerators profile template)
        ((InternalSamples.ofList (saved.paths.get i)).map terminalPoint) first := by
  rw [IndexedRecordStream.map,internalSamples_ofFn,IndexedRecordStream.ofFn]
  unfold terminalStream
  rw [←List.map_coe_finRange_eq_range,List.flatMap_map]
  apply List.flatMap_congr
  intro k _
  have hk : k.val+1<(saved.paths.get i).length := by have := k.isLt;omega
  have hk' := hp (saved.paths.get i)[k.val+1] (List.getElem_mem hk)
  simp only [recordBits]
  congr 1
  unfold GeometryOutput.terminalBits centerBits
  rw [hword,show pathOffset saved i.val+4+3*k.val=pathOffset saved i.val+1+3*(k.val+1) by omega,
    internal_record_coordinate saved constants B L d t hL hshift hscale i (k.val+1) hk hk' 0,
    internal_record_coordinate saved constants B L d t hL hshift hscale i (k.val+1) hk hk' 1,
    internal_record_coordinate saved constants B L d t hL hshift hscale i (k.val+1) hk hk' 2]

 theorem mediator_stream_eq (i : Fin e) (first : ℕ)
    (hp : ∀x∈saved.paths.get i,∀j,0≤shiftedPoint x j) :
    mediatorStream (packedVector saved) constants P numerators profile template
        (pathOffset saved i.val+1) first ((saved.paths.get i).length-1)=
      IndexedRecordStream.bits (recordBits B L d t P numerators profile template)
        ((Segments.ofList (saved.paths.get i)).map mediatorPoint) first := by
  rw [IndexedRecordStream.map,stepSamples_ofFn,IndexedRecordStream.ofFn]
  unfold mediatorStream
  rw [←List.map_coe_finRange_eq_range,List.flatMap_map]
  apply List.flatMap_congr
  intro k _
  have hk : k.val+1<(saved.paths.get i).length := by have := k.isLt;omega
  have hk0 := hp (saved.paths.get i)[k.val] (List.getElem_mem (by omega : k.val<(saved.paths.get i).length))
  have hk1 := hp (saved.paths.get i)[k.val+1] (List.getElem_mem hk)
  simp only [recordBits]
  congr 1
  unfold GeometryOutput.mediatorBits centerBits
  rw [hword,
    mediator_record_coordinate saved constants B L d t hL hshift hscale i k.val hk hk0 hk1 0,
    mediator_record_coordinate saved constants B L d t hL hshift hscale i k.val hk hk0 hk1 1,
    mediator_record_coordinate saved constants B L d t hL hshift hscale i k.val hk hk0 hk1 2]

end
#print axioms originals_stream_eq
#print axioms internal_stream_eq
#print axioms mediator_stream_eq
end Maxwell.Continuum.WellOutput
