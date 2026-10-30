import Maxwell.Continuum.CalibrationSupercellKernel
import Maxwell.Continuum.CalibrationSupercellSymbol
import Maxwell.Continuum.CalibrationCellAssembly

/-! The physical supercell inverse has exactly the finite-grid cell
blocks of the all-image continuum inverse. -/

noncomputable section
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber CellGauge CellBandFourier PeriodicSampling Auxiliary Bloch MasterConstants

variable (M : ℕ) [NeZero M]

attribute [local irreducible] physicalOperator actualGridInverse periodizedCellBlock finiteGridCellBlock

theorem physicalOperator_grid_cell {h z σ : ℝ} (D : Auxiliary.Calibration h z)
    (hσ0 : 0≤σ) (hσ : σ≤h^4/64) (a b : Grid M) (f : CellFieldL2) :
    restrictLatticeCell (representative M a)
      (physicalOperator M (fun j => actualGridInverse z σ (fun i => centeredGrid M (j i)))
        (embedLatticeCell (representative M b) f))=
      (1/8 : ℂ) • finiteGridCellBlock D hσ0 hσ M (representative M a) (representative M b) f := by
  rw [physicalOperator_cell]
  simp_rw [cellPhase_product,cellUnitary_gridInverse M D hσ0 hσ]
  unfold finiteGridCellBlock Product.coefficient
  simp only [Fintype.card_fin,smul_apply,sum_apply,Finset.smul_sum,smul_smul]
  apply Finset.sum_congr
  · ext j
    simp only [Finset.mem_univ]
  · intro j _
    congr 1
    ring

theorem physicalOperator_grid_cell_of_represented {h z σ : ℝ}
    (D : Auxiliary.Calibration h z) (hσ0 : 0≤σ) (hσ : σ≤h^4/64)
    (a b : Bloch.Alias)
    (ha : representative M (Product.frequency M a)=a)
    (hb : representative M (Product.frequency M b)=b) (f : CellFieldL2) :
    restrictLatticeCell a
      (physicalOperator M (fun j => actualGridInverse z σ (fun i => centeredGrid M (j i)))
        (embedLatticeCell b f))=
      (1/8 : ℂ) • finiteGridCellBlock D hσ0 hσ M a b f := by
  simpa only [ha,hb] using physicalOperator_grid_cell M D hσ0 hσ
    (Product.frequency M a) (Product.frequency M b) f

theorem physicalOperator_compression {L z σ : ℝ} (hL : Ls≤L)
    (D : Auxiliary.Calibration L⁻¹ z) (hσ0 : 0≤σ) (hσ : σ≤(L⁻¹)^4/64)
    (hM : L≤(M : ℝ)) (hEven : Even M) (s t : Finset Bloch.Alias)
    (hs : ∀ a∈s, representative M (Product.frequency M a)=a)
    (ht : ∀ b∈t, representative M (Product.frequency M b)=b)
    (hd : ∀ a∈s, ∀ b∈t, ∀ j : Bloch.Alias, j≠0 →
      (M : ℝ)*(imageRadius j : ℝ)/4≤‖integerVector ((b+M • j)-a)‖) :
    (familyProjection s).comp
      ((physicalOperator M (fun j => actualGridInverse z σ (fun i => centeredGrid M (j i)))).comp
        (familyProjection t))=periodizedCompression D hσ0 hσ M s t := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [ContinuousLinearMap.comp_apply,familyProjection_apply,periodizedCompression,sum_apply,
    map_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [periodizedCellBlock_eq_finiteGrid hL D hσ0 hσ M hM hEven a b (hd a ha b hb)]
  change embedLatticeCell a (restrictLatticeCell a
    (physicalOperator M (fun j => actualGridInverse z σ (fun i => centeredGrid M (j i)))
      (embedLatticeCell b (restrictLatticeCell b f))))=_
  rw [physicalOperator_grid_cell_of_represented M D hσ0 hσ a b (hs a ha) (ht b hb),map_smul]
  rfl

#print axioms physicalOperator_compression

end Maxwell.Continuum.Calibration.Supercell
