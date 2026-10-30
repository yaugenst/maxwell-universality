import Maxwell.Continuum.CalibrationTorusCoefficients
import Maxwell.Continuum.CalibrationPeriodizedCell
import Maxwell.Continuum.PeriodicSamplingImages

/-! Exact finite Bloch-grid formula for the literal all-image cell
inverse. The antiperiodic corner carrier is retained, and the even
torus size is used explicitly to preserve it under periodic images. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Calibration

open Auxiliary Bloch CellGauge CellBandFourier MasterConstants UnitAddTorus
open PeriodicSampling

theorem carrier_even_image (M : ℕ) (hM : Even M) (j : Bloch.Alias) :
    carrier (latticeShift (M • j)) = 1 := by
  obtain ⟨m, rfl⟩ := hM
  unfold carrier
  convert Complex.exp_int_mul_two_pi_mul_I ((m : ℤ)*(∑ i : Fin 3, j i)) using 1
  congr 1
  simp [latticeShift, integerVector, Fin.sum_univ_three, smul_eq_mul]
  ring

theorem image_carrier (M : ℕ) (hM : Even M) (a b j : Bloch.Alias) :
    carrier (latticeShift a-latticeShift (b+M • j)) = carrier (latticeShift a-latticeShift b) := by
  have he : latticeShift a-latticeShift (b+M • j) =
      (latticeShift a-latticeShift b)+latticeShift (M • (-j)) := by
    apply PiLp.ext
    intro i
    simp [latticeShift, integerVector, smul_eq_mul]
    ring
  rw [he, carrier_add, carrier_even_image M hM, mul_one]

def finiteGridCellBlock {h z σ : ℝ} (D : Auxiliary.Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (M : ℕ) [NeZero M] (a b : Bloch.Alias) : CellMap :=
  ((8 : ℂ)*carrier (latticeShift a-latticeShift b)) •
    Product.coefficient M (fun j => torusCellSymbol D hσ0 hσ
      (fun i => ((((j i).val : ℝ)/(M : ℝ) : ℝ) : UnitAddCircle))) (Product.frequency M (b-a))

theorem periodizedCellBlock_eq_finiteGrid {L z σ : ℝ} (hL : Ls ≤ L)
    (D : Auxiliary.Calibration L⁻¹ z) (hσ0 : 0 ≤ σ) (hσ : σ ≤ (L⁻¹)^4/64)
    (M : ℕ) [NeZero M] (hM : L ≤ (M : ℝ)) (hEven : Even M) (a b : Bloch.Alias)
    (hd : ∀ j : Bloch.Alias, j ≠ 0 →
      (M : ℝ)*(imageRadius j : ℝ)/4 ≤ ‖integerVector ((b+M • j)-a)‖) :
    periodizedCellBlock D hσ0 hσ M a b = finiteGridCellBlock D hσ0 hσ M a b := by
  rw [periodizedCellBlock_eq_tsum hL D hσ0 hσ M hM a b hd]
  unfold finiteGridCellBlock
  rw [Product.coefficient_continuous_images M _ (torusCellSymbol_coefficients_summable hL D hσ0 hσ),
    ← tsum_const_smul'']
  apply tsum_congr
  intro j
  rw [resolventCellBlock_coefficient, image_carrier M hEven]
  congr 2
  funext i
  simp [Product.aliasEmbedding]
  ring

#print axioms periodizedCellBlock_eq_finiteGrid

end Maxwell.Continuum.Calibration
