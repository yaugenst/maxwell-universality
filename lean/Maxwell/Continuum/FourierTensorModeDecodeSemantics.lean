import Maxwell.Continuum.FourierTensorModeDecode
import Maxwell.Continuum.FourierTensorModeWidths

/-! The runtime decoder reads the same alias and component as the finite
calibration table enumeration. Its extra polarization register does not
alter any of the five emitted tensor-input values. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeDecode
open Maxwell.Cost RationalDataflow PartArray Calibration
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

theorem combined_at (v : ℕ→Parts) (n : ℕ→ℕ) (i : ℕ) (hi : i∈ModeIndex.ports) :
    combined v n i=n i := by simp only [combined,ite_eq_left hi]

theorem decoded_eq (v : ℕ→Parts) (n : ℕ→ℕ) (R : ℕ) (i : Fin (aliasArraySize R))
    (hR : n 311=R) (hi : n 310=i.val) :
    decoded v n=Function.update (Function.update (Function.update (Function.update v
      13 (RawFree.coordinatePart R i 0)) 14 (RawFree.coordinatePart R i 1))
      15 (RawFree.coordinatePart R i 2)) 23 ⟨(arrayPolarizationAt R i).val,0,1⟩ := by
  have radius : ArrayDecodeMachine.output (combined v n) 311=R := by
    rw [ArrayDecodeMachine.output_radius,combined_at v n 311 (by decide),hR]
  have coords (k : Fin 3) := ArrayDecodeMachine.output_coordinates (combined v n) k
  simp only [combined_at v n 311 (by decide),combined_at v n 310 (by decide),hR,hi] at coords
  have h0 := coords 0
  have h1 := coords 1
  have h2 := coords 2
  change ArrayDecodeMachine.output (combined v n) 317=decodedCoordinates R i.val 0 at h0
  change ArrayDecodeMachine.output (combined v n) 319=decodedCoordinates R i.val 1 at h1
  change ArrayDecodeMachine.output (combined v n) 320=decodedCoordinates R i.val 2 at h2
  have pol : ArrayDecodeMachine.output (combined v n) 316=(arrayPolarizationAt R i).val := by
    rw [ArrayDecodeMachine.output_polarization,combined_at v n 310 (by decide),hi,
      arrayPolarizationAt_decode]
  simp only [decoded,ArrayDecodeMachine.loadedParts,radius,h0,h1,h2,pol,coordinatePart_decode]

def rowValues (R : ℕ) (a : Table (2*aliasArraySize R)) (j : Fin 3)
    (r : Fin (RowArithmetic.rowCount R)) (v : ℕ→Parts) : ℕ→Parts :=
  decoded (ModeIndex.readValues R a j r v) (ModeIndex.values j R (aliasArraySize R) r.val)

theorem rowValues_eq (R : ℕ) (a : Table (2*aliasArraySize R)) (j : Fin 3)
    (r : Fin (RowArithmetic.rowCount R)) (v : ℕ→Parts) :
    rowValues R a j r v=Function.update (RowArithmetic.loaded R a j r v) 23 ⟨j.val,0,1⟩ := by
  rw [rowValues,decoded_eq _ _ R (RowArithmetic.rowIndex R j r)
    (ModeIndex.values_radius _ _ _ _) (by rw [ModeIndex.values_real,RowArithmetic.rowIndex_value])]
  simp only [arrayPolarizationAt,RowArithmetic.rowIndex,Equiv.symm_apply_apply,
    RowArithmetic.loaded,ModeIndex.readValues]

theorem output_row (P R : ℕ) (a : Table (2*aliasArraySize R)) (j : Fin 3)
    (r : Fin (RowArithmetic.rowCount R)) (v : ℕ→Parts) (k : ℕ)
    (hk : k∈({4,5,6,9,10}:Finset ℕ)) :
    RowArithmetic.output P (rowValues R a j r v) k=
      RowArithmetic.output P (RowArithmetic.loaded R a j r v) k := by
  rw [rowValues_eq]
  simp only [Finset.mem_insert,Finset.mem_singleton] at hk
  rcases hk with rfl|rfl|rfl|rfl|rfl <;>
    simp [RowArithmetic.output,RowArithmetic.products_values]

theorem output_row_amplitude_width (M P B R : ℕ) [NeZero M]
    (a : Table (2*aliasArraySize R)) (j : Fin 3) (r : Fin (RowArithmetic.rowCount R))
    (v : ℕ→Parts) (hnorm : (v 0).value=Supercell.physicalFactorApprox M P)
    (ha : ‖(GlobalPower.tableData R a).value‖≤2) :
    (RowArithmetic.output B (rowValues R a j r v) 9).Width (B+6) ∧
      (RowArithmetic.output B (rowValues R a j r v) 10).Width (B+6) := by
  rw [output_row B R a j r v 9 (by decide),output_row B R a j r v 10 (by decide)]
  exact RowArithmetic.output_amplitude_width M P B R a j r v hnorm ha

#print axioms rowValues_eq
#print axioms output_row_amplitude_width
end Maxwell.Continuum.Profile.WaveMachine.Runtime.ModeDecode
