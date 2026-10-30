import Maxwell.Continuum.FourierTensorRowArithmetic
import Maxwell.Continuum.CalibrationNormalizedMode
import Maxwell.Continuum.CalibrationCompactOutput
import Maxwell.Continuum.CalibrationRawCoordinates

/-! The concrete row semantics of the tensor compiler, derived directly
from the finite calibration's real/imaginary output array. The alias order
is the same executable product enumeration as the calibration machine. -/
namespace Maxwell.Continuum.Profile.WaveMachine.Runtime.RowArithmetic
open Maxwell.Cost RationalDataflow RationalDataflow.PartArray Calibration
open FreeFiber
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency true

def rowCount (R : ℕ) : ℕ := aliasSide R*(aliasSide R*aliasSide R)
def rowEquiv (R : ℕ) :
    (Fin (aliasSide R) × Fin (aliasSide R) × Fin (aliasSide R)) ≃ Fin (rowCount R) :=
  (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv

def rowIndex (R : ℕ) (j : Fin 3) (r : Fin (rowCount R)) : Fin (aliasArraySize R) :=
  aliasArrayEquiv R ((rowEquiv R).symm r,j)

def rowAlias (R : ℕ) (r : Fin (rowCount R)) : Alias :=
  arrayAlias R ((rowEquiv R).symm r)

theorem rowIndex_value (R : ℕ) (j : Fin 3) (r : Fin (rowCount R)) :
    (rowIndex R j r).val=3*r.val+j.val := by
  change (finProdFinEquiv ((rowEquiv R) ((rowEquiv R).symm r),j)).val=_
  rw [Equiv.apply_symm_apply]
  simp [finProdFinEquiv,Nat.mul_comm,Nat.add_comm]

theorem rowIndex_alias (R : ℕ) (j : Fin 3) (r : Fin (rowCount R)) :
    arrayAliasAt R (rowIndex R j r)=rowAlias R r := by
  simp only [arrayAliasAt,rowIndex,Equiv.symm_apply_apply,rowAlias]

theorem table_coordinate (R : ℕ) (a : Table (2*aliasArraySize R))
    (j : Fin 3) (r : Fin (rowCount R)) :
    (GlobalPower.tableData R a).field (rowAlias R r) j=
      ((a.get (GlobalPower.realIndex R (0,rowIndex R j r))).value,
       (a.get (GlobalPower.realIndex R (1,rowIndex R j r))).value) := by
  have h := GlobalPower.entry_embed R (fun i => (a.get i).value) (rowIndex R j r)
  simpa only [GlobalPower.entry,rowIndex,Equiv.symm_apply_apply,GlobalPower.embed,
    GlobalPower.tableData,FourierData.field,rowAlias] using h

def loaded (R : ℕ) (a : Table (2*aliasArraySize R)) (j : Fin 3)
    (r : Fin (rowCount R)) (v : ℕ→Parts) : ℕ→Parts :=
  Function.update (Function.update (Function.update (Function.update (Function.update v
    2 (a.get (GlobalPower.realIndex R (0,rowIndex R j r))))
    3 (a.get (GlobalPower.realIndex R (1,rowIndex R j r))))
    13 (RawFree.coordinatePart R (rowIndex R j r) 0))
    14 (RawFree.coordinatePart R (rowIndex R j r) 1))
    15 (RawFree.coordinatePart R (rowIndex R j r) 2)

theorem loaded_coordinate (R : ℕ) (a : Table (2*aliasArraySize R)) (j : Fin 3)
    (r : Fin (rowCount R)) (v : ℕ→Parts) (k : Fin 3) :
    loaded R a j r v (13+k.val)=RawFree.coordinatePart R (rowIndex R j r) k := by
  fin_cases k <;> simp [loaded]

theorem loaded_good (R : ℕ) (a : Table (2*aliasArraySize R)) (j : Fin 3)
    (r : Fin (rowCount R)) (v : ℕ→Parts) (hv : Good bank v)
    (ha : ∀i,(a.get i).Valid) : Good bank (loaded R a j r v) :=
  ((((hv.update 2 (ha _)).update 3 (ha _)).update
    13 (RawFree.coordinatePart_valid _ _ _)).update
    14 (RawFree.coordinatePart_valid _ _ _)).update 15 (RawFree.coordinatePart_valid _ _ _)

theorem loaded_width (R : ℕ) (a : Table (2*aliasArraySize R)) (j : Fin 3)
    (r : Fin (rowCount R)) (v : ℕ→Parts) (W : ℕ) (hv : WidthBank bank W v)
    (ha : ∀i,(a.get i).Width W) (hR : R.bits.length+2≤W) :
    WidthBank bank W (loaded R a j r v) :=
  ((((hv.update 2 (ha _)).update 3 (ha _)).update
    13 ((RawFree.coordinatePart_width _ _ _).mono hR)).update
    14 ((RawFree.coordinatePart_width _ _ _).mono hR)).update
    15 ((RawFree.coordinatePart_width _ _ _).mono hR)

theorem output_mode_frequency (M P R : ℕ) (L : ℚ) (a : Table (2*aliasArraySize R))
    (j : Fin 3) (r : Fin (rowCount R)) (v : ℕ→Parts)
    (hscale : (v 1).value=L/(2*M)) (k : Fin 3) :
    (output P (loaded R a j r v) (4+k.val)).value=Supercell.templateFrequency M L (rowAlias R r) k := by
  rw [output_frequency,Parts.mul_value,loaded_coordinate,RawFree.coordinatePart_value,rowIndex_alias]
  have hs : loaded R a j r v 1=v 1 := by simp [loaded]
  rw [hs,hscale]
  unfold Supercell.templateFrequency
  ring

theorem output_mode_amplitudes (M P B R : ℕ) (a : Table (2*aliasArraySize R))
    (j : Fin 3) (r : Fin (rowCount R)) (v : ℕ→Parts)
    (hnorm : (v 0).value=Supercell.physicalFactorApprox M P) :
    let c := roundFourierCoefficient B (Supercell.physicalCoefficientData M P (GlobalPower.tableData R a))
      (rowAlias R r) j
    output B (loaded R a j r v) 9=Parts.literal (c.1.numerator:ℚ) ∧
    output B (loaded R a j r v) 10=Parts.literal (c.2.numerator:ℚ) := by
  dsimp only
  rw [output_real,output_imag]
  have h0 : loaded R a j r v 0=v 0 := by simp [loaded]
  have h2 : loaded R a j r v 2=a.get (GlobalPower.realIndex R (0,rowIndex R j r)) := by simp [loaded]
  have h3 : loaded R a j r v 3=a.get (GlobalPower.realIndex R (1,rowIndex R j r)) := by simp [loaded]
  rw [h0,h2,h3,hnorm]
  simp only [roundFourierCoefficient,Supercell.physicalCoefficientData,FourierData.scale_field]
  change _=Parts.literal ((roundDyadic B
      (Supercell.physicalFactorApprox M P*((GlobalPower.tableData R a).field (rowAlias R r) j).1)).numerator:ℚ) ∧
    _=Parts.literal ((roundDyadic B
      (Supercell.physicalFactorApprox M P*((GlobalPower.tableData R a).field (rowAlias R r) j).2)).numerator:ℚ)
  rw [table_coordinate]
  exact ⟨rfl,rfl⟩

#print axioms output_mode_frequency
#print axioms output_mode_amplitudes
end Maxwell.Continuum.Profile.WaveMachine.Runtime.RowArithmetic
