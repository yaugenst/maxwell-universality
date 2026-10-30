import Maxwell.Continuum.SourceGeometryLookup
import Maxwell.Continuum.StoredGeometryMediator

/-! The actual words read by the geometry machine compute the same integer
centers as the continuum construction, for both kinds of decorated wells. -/
namespace Maxwell.Composition.SourceDecorationEnumeration
open Maxwell.Logical Maxwell.Logical.Routing Maxwell.Spectral.Lattice Maxwell.Cost
open Maxwell.Continuum.GeometryOutput
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

theorem listValue_pointWords (p : Point) (hp : ∀k,0≤shiftedPoint p k) (j : Fin 3) :
    (listValue (pointWords p) j.val:ℤ)=shiftedPoint p j := by
  have hj : j.val<(pointWords p).length := by rw [pointWords_length];exact j.isLt
  simp only [listValue,List.getElem?_eq_getElem hj,Option.getD_some]
  exact pointWords_value p hp j

theorem terminalCoordinate_eq_center {v e : ℕ} (saved : SourceEmission.Geometry v e)
    (constants : ℕ→ℕ) (B : Fin 3→ℕ) (L d t cursor : ℕ) (hL : Even L)
    (hs : constants 982=L+L*t+8) (hscale : ∀j:Fin 3,constants (983+j.val)=2*L*d*B j)
    (p : Point) (hp : ∀j,0≤shiftedPoint p j)
    (hread : ∀j:Fin 3,arrayValue (packedVector saved) (cursor+j.val)=listValue (pointWords p) j.val)
    (j : Fin 3) :
    (terminalCoordinate (packedVector saved) constants cursor j:ℤ)=
      centerPoint (fun k=>(B k:ℤ)) L d t (terminalPoint p) j := by
  rw [centerPoint_even _ hL]
  simp only [terminalCoordinate,hs,hscale,hread,terminalPoint]
  push_cast
  rw [listValue_pointWords p hp j]

theorem mediatorCoordinate_eq_center {v e : ℕ} (saved : SourceEmission.Geometry v e)
    (constants : ℕ→ℕ) (B : Fin 3→ℕ) (L d t cursor : ℕ) (hL : Even L)
    (hs : constants 982=L+L*t+8) (hscale : ∀j:Fin 3,constants (983+j.val)=2*L*d*B j)
    (p q : Point) (hp : ∀j,0≤shiftedPoint p j) (hq : ∀j,0≤shiftedPoint q j)
    (hreadp : ∀j:Fin 3,arrayValue (packedVector saved) (cursor+j.val)=listValue (pointWords p) j.val)
    (hreadq : ∀j:Fin 3,arrayValue (packedVector saved) (cursor+3+j.val)=listValue (pointWords q) j.val)
    (j : Fin 3) :
    (mediatorCoordinate (packedVector saved) constants cursor j:ℤ)=
      centerPoint (fun k=>(B k:ℤ)) L d t (mediatorPoint (p,q)) j := by
  rw [centerPoint_even _ hL]
  simp only [mediatorCoordinate,hs,hscale,hreadp,hreadq,mediatorPoint,Pi.add_apply]
  push_cast
  rw [listValue_pointWords p hp j,listValue_pointWords q hq j]

theorem original_record_coordinate {v e : ℕ} (saved : SourceEmission.Geometry v e)
    (constants : ℕ→ℕ) (B : Fin 3→ℕ) (L d t : ℕ) (hL : Even L)
    (hs : constants 982=L+L*t+8) (hscale : ∀j:Fin 3,constants (983+j.val)=2*L*d*B j)
    (i : Fin v) (hp : ∀j,0≤shiftedPoint (saved.original.get i) j) (j : Fin 3) :
    (terminalCoordinate (packedVector saved) constants (3*i.val) j:ℤ)=
      centerPoint (fun k=>(B k:ℤ)) L d t (terminalPoint (saved.original.get i)) j :=
  terminalCoordinate_eq_center saved constants B L d t (3*i.val) hL hs hscale
    _ hp (original_lookup saved i) j

theorem internal_record_coordinate {v e : ℕ} (saved : SourceEmission.Geometry v e)
    (constants : ℕ→ℕ) (B : Fin 3→ℕ) (L d t : ℕ) (hL : Even L)
    (hs : constants 982=L+L*t+8) (hscale : ∀j:Fin 3,constants (983+j.val)=2*L*d*B j)
    (i : Fin e) (k : ℕ) (hk : k<(saved.paths.get i).length)
    (hp : ∀j,0≤shiftedPoint (saved.paths.get i)[k] j) (j : Fin 3) :
    (terminalCoordinate (packedVector saved) constants (pathOffset saved i.val+1+3*k) j:ℤ)=
      centerPoint (fun k=>(B k:ℤ)) L d t (terminalPoint (saved.paths.get i)[k]) j :=
  terminalCoordinate_eq_center saved constants B L d t _ hL hs hscale _ hp
    (path_point_lookup saved i k hk) j

theorem mediator_record_coordinate {v e : ℕ} (saved : SourceEmission.Geometry v e)
    (constants : ℕ→ℕ) (B : Fin 3→ℕ) (L d t : ℕ) (hL : Even L)
    (hs : constants 982=L+L*t+8) (hscale : ∀j:Fin 3,constants (983+j.val)=2*L*d*B j)
    (i : Fin e) (k : ℕ) (hk : k+1<(saved.paths.get i).length)
    (hp : ∀j,0≤shiftedPoint (saved.paths.get i)[k] j)
    (hq : ∀j,0≤shiftedPoint (saved.paths.get i)[k+1] j) (j : Fin 3) :
    (mediatorCoordinate (packedVector saved) constants (pathOffset saved i.val+1+3*k) j:ℤ)=
      centerPoint (fun k=>(B k:ℤ)) L d t
        (mediatorPoint ((saved.paths.get i)[k],(saved.paths.get i)[k+1])) j := by
  apply mediatorCoordinate_eq_center saved constants B L d t _ hL hs hscale _ _ hp hq
  · intro l;exact path_point_lookup saved i k (by omega) l
  · intro l
    rw [show pathOffset saved i.val+1+3*k+3+l.val=pathOffset saved i.val+1+3*(k+1)+l.val by omega]
    exact path_point_lookup saved i (k+1) hk l

#print axioms original_record_coordinate
#print axioms mediator_record_coordinate
end Maxwell.Composition.SourceDecorationEnumeration
