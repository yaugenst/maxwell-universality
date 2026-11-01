import Maxwell.Continuum.CalibrationInverseOutputGather
import Maxwell.Continuum.CalibrationSchurExpression

/-! The 144 fixed neighbor reads needed by a central Schur column. Each
retained cell is identified with its actual cached inverse entry. -/
namespace Maxwell.Continuum.Calibration.SchurGather
open Maxwell.Cost Maxwell.Cost.Structured Maxwell.Cost.CalibrationMatrix
open RationalDataflow FreeFiber NeumannMachine OutputGather
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def request (row : Fin 24) (j : Fin 3) (plus : Bool) : Request :=
  ⟨SchurExpression.neighbor row j plus,SchurExpression.neighbor_bounds row j plus,
    BasisForcing.polarization row,SchurExpression.neighborRegister row j plus⟩
def requests : List Request :=
  (List.finRange 24).flatMap (fun row=>(List.finRange 3).flatMap (fun j=>[request row j true,request row j false]))

theorem request_mem (row : Fin 24) (j : Fin 3) (plus : Bool) : request row j plus∈requests := by
  apply List.mem_flatMap.mpr
  refine ⟨row,by simp,?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨j,by simp,?_⟩
  cases plus <;> simp

theorem request_cases {r : Request} (h:r∈requests) :
    ∃row j plus,r=request row j plus := by
  obtain ⟨row,_,h⟩:=List.mem_flatMap.mp h
  obtain ⟨j,_,h⟩:=List.mem_flatMap.mp h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with h|h
  · exact ⟨row,j,true,h⟩
  · exact ⟨row,j,false,h⟩

theorem target_unique (row row' : Fin 24) (j j' : Fin 3) (plus plus' : Bool)
    (eq:(request row j plus).target=(request row' j' plus').target) :
    request row j plus=request row' j' plus' := by
  change 240+6*row.val+2*j.val+(if plus then 0 else 1)=
    240+6*row'.val+2*j'.val+(if plus' then 0 else 1) at eq
  cases plus <;> cases plus' <;> simp only [Bool.false_eq_true,↓reduceIte] at eq
  all_goals have hr:row=row':=Fin.ext (by omega)
  all_goals have hj:j=j':=Fin.ext (by omega)
  all_goals first | omega | subst row';subst j';rfl

theorem targets (r : Request) (h:r∈requests) : 240≤r.target ∧ r.target<384 := by
  obtain ⟨row,j,plus,rfl⟩:=request_cases h
  change 240≤240+6*row.val+2*j.val+(if plus then 0 else 1) ∧
    240+6*row.val+2*j.val+(if plus then 0 else 1)<384
  cases plus <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega

theorem retained {N D : ℕ} (a : Snapshot (aliasArraySize (N+3))) (p : ℕ→Parts)
    (row : Fin 24) (j : Fin 3) (plus : Bool) :
    OutputGather.parts a D requests p (SchurExpression.neighborRegister row j plus)=
      (request row j plus).parts a D := by
  apply parts_at a requests p (request row j plus) (request_mem row j plus)
  intro r hr eq
  obtain ⟨row',j',plus',rfl⟩:=request_cases hr
  rw [target_unique row' row j' j plus' plus eq]

theorem retained_value {N D : ℕ} (a : Snapshot (aliasArraySize (N+3))) (p : ℕ→Parts)
    (row : Fin 24) (j : Fin 3) (plus : Bool) :
    (OutputGather.parts a D requests p (SchurExpression.neighborRegister row j plus)).value=
      extendAliasArray (N+3)
        (Vector.ofFn (fun k=>((Horner.channels a.words 10 11).value k:ℚ)/(D:ℚ)))
        (SchurExpression.neighbor row j plus) (BasisForcing.polarization row) := by
  rw [retained,Request.parts,OutputRead.entryParts_value]
  simp only [extendAliasArray,request,Request.index,OutputIndex.in_cube N _ (SchurExpression.neighbor_bounds row j plus),↓reduceDIte,
    vector_get_ofFn,OutputIndex.index]

theorem scalar_kept {N D : ℕ} (a : Snapshot (aliasArraySize (N+3))) (p : ℕ→Parts)
    (i : ℕ) (hi:i<240) : OutputGather.parts a D requests p i=p i := by
  apply parts_keep
  intro r hr
  have h:240≤r.target:=(targets r hr).1
  omega

#print axioms retained_value
end Maxwell.Continuum.Calibration.SchurGather
