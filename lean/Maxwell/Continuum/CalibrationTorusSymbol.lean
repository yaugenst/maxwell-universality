import Maxwell.Continuum.PeriodicEuclideanFourier
import Maxwell.Continuum.FullCellGevrey
import Maxwell.Continuum.FullCellKernel

/-! The literal complete cutoff Maxwell inverse as a continuous symbol
on the unit quasi-momentum torus, with its exact Fourier coefficients. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Calibration

open Auxiliary Bloch CellGauge CellBandFourier FreeFiber PeriodicBand PeriodicSampling
open MeasureTheory UnitAddTorus OperatorFourier
open scoped InnerProduct

local instance torusCellSymbolRealSpace : NormedSpace ℝ CellMap := NormedSpace.complexToReal

attribute [local irreducible] cutoffFullCellSymbol fullCellSymbol

def scaledCutoffSymbol (z σ : ℝ) (x : Fin 3 → ℝ) : CellMap :=
  cutoffFullCellSymbol z σ (Real.pi • WithLp.toLp 2 x)

theorem scaledCutoffSymbol_continuous {h z σ : ℝ} (D : Auxiliary.Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) : Continuous (scaledCutoffSymbol z σ) := by
  have hi : Continuous (fun x : Fin 3 → ℝ => Real.pi • (WithLp.toLp 2 x : Space)) := by fun_prop
  exact (cutoffFullCellSymbol_continuous D hσ0 hσ).comp hi

theorem scaledCutoffSymbol_zero (z σ : ℝ) (x : Fin 3 → ℝ)
    (hx : ∃ i, (1/4 : ℝ) ≤ |x i|) : scaledCutoffSymbol z σ x = 0 := by
  obtain ⟨i, hi⟩ := hx
  have hz : cutoff (Real.pi • WithLp.toLp 2 x) = 0 := by
    by_contra hn
    have hb := cutoff_ne_zero_coordinate_lt hn i
    change |Real.pi*x i| < 2*smallRadius at hb
    rw [abs_mul, abs_of_pos Real.pi_pos] at hb
    have hr : 2*smallRadius ≤ (1/2 : ℝ) := by norm_num [smallRadius, backgroundAmplitude]
    nlinarith [Real.pi_gt_three]
  unfold scaledCutoffSymbol cutoffFullCellSymbol cutoffSymbol
  rw [hz, Complex.ofReal_zero]
  exact zero_smul ℂ (realSymbol (fullCellSymbol z σ) (Real.pi • WithLp.toLp 2 x))

def torusCellSymbol {h z σ : ℝ} (D : Auxiliary.Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) : C(UnitAddTorus (Fin 3), CellMap) :=
  centeredContinuousLift (scaledCutoffSymbol z σ) (scaledCutoffSymbol_continuous D hσ0 hσ)
    (scaledCutoffSymbol_zero z σ)

theorem torusCellSymbol_coefficient_integral {h z σ : ℝ} (D : Auxiliary.Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (n : Bloch.Alias) :
    mFourierCoeff (torusCellSymbol D hσ0 hσ) n =
      ∫ x : Fin 3 → ℝ, Product.phase (-n) x • cutoffFullCellSymbol z σ (Real.pi • WithLp.toLp 2 x) :=
  centeredLift_coefficient (scaledCutoffSymbol z σ) (scaledCutoffSymbol_continuous D hσ0 hσ)
    (scaledCutoffSymbol_zero z σ) n

theorem torusCellSymbol_coefficient {h z σ : ℝ} (D : Auxiliary.Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (n : Bloch.Alias) :
    mFourierCoeff (torusCellSymbol D hσ0 hσ) n =
      (Real.pi^3)⁻¹ • angularFourier (cutoffFullCellSymbol z σ) (latticeShift n) := by
  rw [torusCellSymbol_coefficient_integral]
  have he := euclidean_scaled_coefficient (cutoffFullCellSymbol z σ) Real.pi Real.pi_pos n
  rw [show 2*Real.pi/Real.pi = 2 by field_simp] at he
  convert! he using 1

#print axioms torusCellSymbol_coefficient

end Maxwell.Continuum.Calibration
