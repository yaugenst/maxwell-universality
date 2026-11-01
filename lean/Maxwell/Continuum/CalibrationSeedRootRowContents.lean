import Maxwell.Continuum.CalibrationSeedRootRowEmission
import Maxwell.Continuum.RationalDataflowRowWriteValues

/-! Exact contents of each emitted row and preservation of the other
rows, using the authoritative real-block/imaginary-block coordinate map. -/
namespace Maxwell.Continuum.Calibration.SeedRoot
open Maxwell.Cost Maxwell.Cost.Structured RationalDataflow
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

theorem outputCoordinate_injective (M D : ℕ)
    (r s : Fin (ArrayDecodeMachine.aliasRowCount (3*M+D))) (j k : Fin 3) (p q : Fin 2) :
    outputCoordinate M D r j p=outputCoordinate M D s k q ↔ r=s ∧ j=k ∧ p=q := by
  constructor
  · intro h
    have he := (GlobalPower.realIndex (3*M+D)).injective h
    have part : p=q := congrArg Prod.fst he
    have rowIndex := congrArg (fun x : Fin 2×Fin (aliasArraySize (3*M+D))=>x.2.val) he
    change 3*r.val+j.val=3*s.val+k.val at rowIndex
    have hj := j.isLt
    have hk := k.isLt
    exact ⟨Fin.ext (by omega),Fin.ext (by omega),part⟩
  · rintro ⟨rfl,rfl,rfl⟩
    rfl

theorem phasesTable_metadata (M D : ℕ) (a : PartArray.Table (2*(2*D+1)^3))
    (row : Fin (ArrayDecodeMachine.aliasRowCount (3*M+D))) (u : Fin 3→ℕ) (v : ℕ→Parts)
    (ps : List (Fin 3×Fin 2)) (b : PartArray.Table (2*aliasArraySize (3*M+D))) :
    (phasesTable M D a row u v ps b).width=b.width ∧
    (phasesTable M D a row u v ps b).basePositive=b.basePositive ∧
    (phasesTable M D a row u v ps b).baseNegative=b.baseNegative ∧
    (phasesTable M D a row u v ps b).baseDenominator=b.baseDenominator ∧
    (phasesTable M D a row u v ps b).clock=b.clock := by
  induction ps generalizing b with
  | nil => exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  | cons p ps ih => exact ih _

theorem phasesTable_get_absent (M D : ℕ) (a : PartArray.Table (2*(2*D+1)^3))
    (row : Fin (ArrayDecodeMachine.aliasRowCount (3*M+D))) (u : Fin 3→ℕ) (v : ℕ→Parts)
    (ps : List (Fin 3×Fin 2)) (b : PartArray.Table (2*aliasArraySize (3*M+D)))
    (i : Fin (2*aliasArraySize (3*M+D)))
    (outside : ∀p∈ps,outputCoordinate M D row p.1 p.2≠i) :
    (phasesTable M D a row u v ps b).get i=b.get i := by
  induction ps generalizing b with
  | nil => rfl
  | cons p ps ih =>
    rw [phasesTable,ih _ (fun q hq=>outside q (List.mem_cons_of_mem _ hq)),PartArray.Table.set_get_ne]
    exact outside p (by simp)

theorem phasesTable_get_present (M D : ℕ) (a : PartArray.Table (2*(2*D+1)^3))
    (row : Fin (ArrayDecodeMachine.aliasRowCount (3*M+D))) (u : Fin 3→ℕ) (v : ℕ→Parts)
    (ps : List (Fin 3×Fin 2)) (b : PartArray.Table (2*aliasArraySize (3*M+D)))
    (fits : ∀p∈ps,(entryParts M D a u p.1 p.2 v).Width (addressValue b.width))
    (p : Fin 3×Fin 2) (hp : p∈ps) :
    (phasesTable M D a row u v ps b).get (outputCoordinate M D row p.1 p.2)=entryParts M D a u p.1 p.2 v := by
  induction ps generalizing b with
  | nil => simp at hp
  | cons q ps ih =>
    by_cases tail : p∈ps
    · exact ih _ (fun x hx=>fits x (List.mem_cons_of_mem _ hx)) tail
    · have eq : p=q := (List.mem_cons.mp hp).resolve_right tail
      subst q
      rw [phasesTable,phasesTable_get_absent,PartArray.Table.set_get]
      · exact fits p (by simp)
      · intro q hq he
        have eq := (outputCoordinate_injective M D row row q.1 p.1 q.2 p.2).mp he
        have pair : q=p := Prod.ext eq.2.1 eq.2.2
        exact tail (pair ▸ hq)

theorem mem_phases (p : Fin 3×Fin 2) : p∈phases := by
  rcases p with ⟨j,p⟩
  fin_cases j <;> fin_cases p <;> decide

theorem emittedRow_get (M D : ℕ) (a : PartArray.Table (2*(2*D+1)^3))
    (row : Fin (ArrayDecodeMachine.aliasRowCount (3*M+D))) (v : ℕ→Parts)
    (b : PartArray.Table (2*aliasArraySize (3*M+D)))
    (fits : ∀p∈phases,(entryParts M D a (decodedCoordinates (3*M+D) (3*row.val)) p.1 p.2 v).Width
      (addressValue b.width)) (j : Fin 3) (p : Fin 2) :
    (emittedRow M D a row v b).get (outputCoordinate M D row j p)=
      entryParts M D a (decodedCoordinates (3*M+D) (3*row.val)) j p v :=
  phasesTable_get_present M D a row _ v phases b fits (j,p) (mem_phases _)

theorem emittedRow_other (M D : ℕ) (a : PartArray.Table (2*(2*D+1)^3))
    (r s : Fin (ArrayDecodeMachine.aliasRowCount (3*M+D))) (different : r≠s) (v : ℕ→Parts)
    (b : PartArray.Table (2*aliasArraySize (3*M+D))) (j : Fin 3) (p : Fin 2) :
    (emittedRow M D a r v b).get (outputCoordinate M D s j p)=b.get (outputCoordinate M D s j p) := by
  apply phasesTable_get_absent
  intro q _ he
  exact different ((outputCoordinate_injective M D r s q.1 j q.2 p).mp he).1

#print axioms emittedRow_get
end Maxwell.Continuum.Calibration.SeedRoot
