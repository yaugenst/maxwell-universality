import Maxwell.Continuum.CalibrationForcingReads
import Maxwell.Continuum.CalibrationForcingVector

/-! The stride-three source traversal agrees with the actual Fourier-array
enumeration and with the literal cached forcing vector. -/

namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine

open RationalDataflow FreeFiber
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def aliasRowCount (R : ℕ) : ℕ := aliasSide R*(aliasSide R*aliasSide R)
def polarizationRow (R : ℕ) (row : Fin (aliasRowCount R)) (j : Fin 3) : Fin (aliasArraySize R) :=
  ⟨3*row.val+j.val,by
    have hr := row.isLt
    have hj := j.isLt
    change 3*row.val+j.val<aliasRowCount R*3
    omega⟩

theorem polarizationRow_div (R : ℕ) (row : Fin (aliasRowCount R)) (j : Fin 3) :
    (polarizationRow R row j).val/3=row.val := by
  change (3*row.val+j.val)/3=row.val
  omega

theorem polarizationRow_polarization (R : ℕ) (row : Fin (aliasRowCount R)) (j : Fin 3) :
    arrayPolarizationAt R (polarizationRow R row j)=j := by
  apply Fin.ext
  rw [arrayPolarizationAt_decode]
  change (3*row.val+j.val)%3=j.val
  omega

theorem polarizationRow_alias (R : ℕ) (row : Fin (aliasRowCount R)) (j : Fin 3) :
    arrayAliasAt R (polarizationRow R row j)=arrayAliasAt R (polarizationRow R row 0) := by
  funext k
  rw [arrayAliasAt_decode,arrayAliasAt_decode]
  simp only [decodedCoordinates,polarizationRow_div]

theorem extend_array_at {V : Type*} [Zero V] (R : ℕ) (a : Vector V (aliasArraySize R))
    (i : Fin (aliasArraySize R)) :
    extendAliasArray R a (arrayAliasAt R i) (arrayPolarizationAt R i)=a.get i := by
  have hi : aliasInCube R (arrayAliasAt R i) := arrayAlias_mem R ((aliasArrayEquiv R).symm i).1
  rw [extendAliasArray,dite_eq_left hi]
  simp only [arrayAliasAt,arrayPolarizationAt,arrayIndex_alias,Prod.mk.eta,Equiv.apply_symm_apply]

def tableSource (R : ℕ) (a : PartArray.Table (aliasArraySize R)) : RationalRealField :=
  extendAliasArray R (Vector.ofFn (fun i => (a.get i).value))

theorem tableSource_row (R : ℕ) (a : PartArray.Table (aliasArraySize R))
    (row : Fin (aliasRowCount R)) (j : Fin 3) :
    tableSource R a (arrayAliasAt R (polarizationRow R row 0)) j=(a.get (polarizationRow R row j)).value := by
  have h := extend_array_at R (Vector.ofFn (fun i => (a.get i).value)) (polarizationRow R row j)
  rw [polarizationRow_alias R row j,polarizationRow_polarization] at h
  simpa only [tableSource,vector_get_ofFn] using h

theorem loaded_forcing_row (R : ℕ) (a : PartArray.Table (aliasArraySize R))
    (row : Fin (aliasRowCount R)) (v : ℕ→Parts) (i : Fin 3) :
    RawFree.forcingCoefficient (sourceLoaded a row.val v) (arrayAliasAt R (polarizationRow R row 0)) i=
      cachedForcing (v 0).value (v 1).value (fun k => (RawFree.quasiParts v k).value)
        R (tableSource R a) (polarizationRow R row i) := by
  have h0 := sourceLoaded_other a row.val v 0 (by decide)
  have h1 := sourceLoaded_other a row.val v 1 (by decide)
  rw [RawFree.forcingCoefficient,h0,h1,sourceLoaded_quasi]
  change (∑ j, rationalFreeInverseMatrix (v 0).value (v 1).value
    (fun k => (RawFree.quasiParts v k).value) (arrayAliasAt R (polarizationRow R row 0)) i j*
      (RawFree.forcingSource (sourceLoaded a row.val v) j).value)=_
  change _=∑ j, rationalFreeInverseMatrix (v 0).value (v 1).value
    (fun k => (RawFree.quasiParts v k).value) (arrayAliasAt R (polarizationRow R row i))
      (arrayPolarizationAt R (polarizationRow R row i)) j*
        tableSource R a (arrayAliasAt R (polarizationRow R row i)) j
  rw [polarizationRow_alias R row i,polarizationRow_polarization]
  apply Finset.sum_congr rfl
  intro j _
  rw [sourceLoaded_source,tableSource_row]
  congr 2
  have hj : 3*row.val+j.val<aliasArraySize R := (polarizationRow R row j).isLt
  rw [PartArray.Table.getD,dite_eq_left hj]
  rfl

#print axioms tableSource_row
#print axioms loaded_forcing_row

end Maxwell.Continuum.Calibration.ArrayDecodeMachine
