import Maxwell.Continuum.CalibrationCoefficientEmission

/-! The emitted raw table is exactly the padded coefficient interface used
by the executed shared-denominator and Neumann algorithms. -/

namespace Maxwell.Continuum.Calibration.ArrayDecodeMachine

open Maxwell.Cost RationalDataflow
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def tableCoefficients {n : ℕ} (c : PartArray.Table (NeumannMachine.tableSize n)) :
    NeumannMachine.CoefficientIndex n→Parts :=
  fun i => c.get (Fin.castAdd n (NeumannMachine.flatIndex n i))

theorem tableCoefficients_padded {n : ℕ} (c : PartArray.Table (NeumannMachine.tableSize n))
    (hz : ∀ i : Fin (NeumannMachine.tableSize n), n+n*n≤ i.val → c.get i=Parts.literal 0) :
    ∀ i, c.get i=NeumannMachine.paddedCoefficients (tableCoefficients c) i := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j
    rw [NeumannMachine.padded_prefix]
    simp only [NeumannMachine.flatCoefficients,tableCoefficients,Equiv.apply_symm_apply]
  · intro j
    rw [NeumannMachine.padded_zero]
    exact hz _ (by simp)

theorem tableCoefficients_source (R : ℕ) (c : PartArray.Table (NeumannMachine.tableSize (aliasArraySize R)))
    (i : Fin (aliasArraySize R)) : tableCoefficients c (.inl i)=
      c.get (sourceSlot R (by unfold NeumannMachine.tableSize; omega) i) := rfl

theorem tableCoefficients_matrix (R : ℕ) (c : PartArray.Table (NeumannMachine.tableSize (aliasArraySize R)))
    (i j : Fin (aliasArraySize R)) : tableCoefficients c (.inr (i,j))=
      c.get (matrixSlot R (by unfold NeumannMachine.tableSize; omega)
        (Maxwell.Cost.CalibrationMatrix.matrixSlot i j)) := by
  rw [tableCoefficients,NeumannMachine.flatIndex_matrix]
  rfl

theorem flatRow_matrixSlot (R : ℕ) (i j : Fin (aliasArraySize R)) :
    flatRow R (Maxwell.Cost.CalibrationMatrix.matrixSlot i j)=i := by
  apply Fin.ext
  change (i.val*aliasArraySize R+j.val)/aliasArraySize R=i.val
  rw [Nat.add_comm,Nat.add_mul_div_right _ _ (aliasArraySize_pos R),Nat.div_eq_of_lt j.isLt,Nat.zero_add]

theorem flatColumn_matrixSlot (R : ℕ) (i j : Fin (aliasArraySize R)) :
    flatColumn R (Maxwell.Cost.CalibrationMatrix.matrixSlot i j)=j := by
  apply Fin.ext
  change (i.val*aliasArraySize R+j.val)%aliasArraySize R=j.val
  exact Nat.mul_add_mod_of_lt j.isLt

theorem tableCoefficients_values (R : ℕ) (c : PartArray.Table (NeumannMachine.tableSize (aliasArraySize R)))
    (t E : ℚ) (r : Fin 3→ℚ) (f : RationalRealField)
    (hsource : ∀ i : Fin (aliasArraySize R),
      (c.get (sourceSlot R (by unfold NeumannMachine.tableSize; omega) i)).Valid ∧
      (c.get (sourceSlot R (by unfold NeumannMachine.tableSize; omega) i)).value=cachedForcing t E r R f i)
    (hmatrix : ∀ k : Fin (aliasArraySize R*aliasArraySize R),
      (c.get (matrixSlot R (by unfold NeumannMachine.tableSize; omega) k)).Valid ∧
      (c.get (matrixSlot R (by unfold NeumannMachine.tableSize; omega) k)).value=
        cachedTransitionMatrix t E r R (flatRow R k) (flatColumn R k)) :
    (∀ i, (tableCoefficients c i).Valid) ∧
      ∀ i, (tableCoefficients c i).value=cachedCoefficientTable t E r R f i := by
  have source (i : Fin (aliasArraySize R)) := hsource i
  have matrix (i j : Fin (aliasArraySize R)) := hmatrix (Maxwell.Cost.CalibrationMatrix.matrixSlot i j)
  constructor
  · rintro (i | ⟨i,j⟩)
    · rw [tableCoefficients_source]
      exact (source i).1
    · rw [tableCoefficients_matrix]
      exact (matrix i j).1
  · rintro (i | ⟨i,j⟩)
    · rw [tableCoefficients_source]
      exact (source i).2
    · rw [tableCoefficients_matrix]
      change _=cachedTransitionMatrix t E r R i j
      simpa only [flatRow_matrixSlot,flatColumn_matrixSlot] using (matrix i j).2

#print axioms tableCoefficients_padded
#print axioms tableCoefficients_values

end Maxwell.Continuum.Calibration.ArrayDecodeMachine
