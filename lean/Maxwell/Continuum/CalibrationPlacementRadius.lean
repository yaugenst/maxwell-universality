import Maxwell.Continuum.WellInteractionLattice
import Maxwell.Continuum.CalibrationLatticeDecay

/-! A computed common supercell radius covers all three actual placement
displacements used by the calibrated useful couplings. -/

namespace Maxwell.Continuum.Calibration

open EffectiveMass PeriodicBand

def couplingRadius (L d : ℕ) : ℕ := 2^53*L*d

theorem placementDiagonal_bound (j : Fin 3) : (placementDiagonal j).natAbs≤2^53 := by
  fin_cases j <;> norm_num [placementDiagonal]

theorem placementCell_radius (L d : ℕ) (ν : Bloch.Alias) :
    imageRadius (placementCell L d ν)≤couplingRadius L d*imageRadius ν := by
  unfold imageRadius
  apply Finset.sup_le
  intro j _
  have hv : (ν j).natAbs≤Finset.univ.sup (fun i : Fin 3 => (ν i).natAbs) :=
    Finset.le_sup (f := fun i : Fin 3 => (ν i).natAbs) (Finset.mem_univ j)
  simp only [placementCell,placementMatrix,Matrix.mulVec_diagonal,
    Int.natAbs_mul,Int.natAbs_natCast]
  calc
    _ ≤ (L*d)*(2^53*Finset.univ.sup (fun i : Fin 3 => (ν i).natAbs)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul (placementDiagonal_bound j) hv)
    _ = _ := by unfold couplingRadius; ring

theorem axial_imageRadius (j : Fin 3) : imageRadius (Pi.single j (1 : ℤ))≤1 := by
  unfold imageRadius
  apply Finset.sup_le
  intro i _
  by_cases hi : i=j <;> simp [hi]

theorem couplingRadius_contains (L d : ℕ) (j : Fin 3) :
    imageRadius (placementCell L d (Pi.single j 1))≤couplingRadius L d :=
  (placementCell_radius L d (Pi.single j 1)).trans
    ((Nat.mul_le_mul_left _ (axial_imageRadius j)).trans_eq (Nat.mul_one _))

theorem couplingRadius_polynomial {L d C ℓ : ℕ} (hL : L≤C*ℓ^6) (hd : d≤C*ℓ) :
    couplingRadius L d≤(2^53*C^2)*ℓ^7 := by
  calc
    _ ≤ 2^53*(C*ℓ^6)*(C*ℓ) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hL) hd
    _ = _ := by ring

#print axioms couplingRadius_contains
#print axioms couplingRadius_polynomial

end Maxwell.Continuum.Calibration
