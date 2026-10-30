import Maxwell.Continuum.PeriodicTubeCellSymbol
import Maxwell.Continuum.PeriodicBandProjectionAnalytic

/-! The actual selected within-cell projection as a rank-one operator.
Both factors retain the literal cell gauge and complete Fourier basis. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.CellGauge

open Complex FreeFiber PeriodicBand FiberNormalization CellBandFourier Auxiliary

attribute [local irreducible] fullSpectralProjection normalizedFiberVector

def selectedCellVector (q : Momentum) : CellFieldL2 :=
  antiGauge q (CellFourier.unitary (normalizedFiberVector (unscale q)))

def selectedCellFunctional (q : Momentum) : CellFieldL2 →L[ℂ] ℂ :=
  (bilinear (normalizedFiberVector (unscale q))).comp
    (CellFourier.unitary.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp (antiUngauge q))

theorem selectedCellProjection_apply {q : Momentum} (hq : q ∈ physicalChart)
    (f : CellFieldL2) :
    selectedCellProjection q f = selectedCellFunctional q f • selectedCellVector q := by
  change antiGauge q (conjugate (fullSpectralProjection (unscale q)) (antiUngauge q f)) = _
  rw [conjugate_apply, fullSpectralProjection_eq_bilinearProjection (unscale_mem_chart hq)]
  change antiGauge q (CellFourier.unitary
    (bilinear (normalizedFiberVector (unscale q))
      (CellFourier.unitary.symm (antiUngauge q f)) • normalizedFiberVector (unscale q))) = _
  rw [map_smul, map_smul]
  rfl

theorem selectedCellProjection_pairing {q : Momentum} (hq : q ∈ physicalChart)
    (g f : CellFieldL2) :
    inner ℂ g (selectedCellProjection q f) =
      selectedCellFunctional q f * inner ℂ g (selectedCellVector q) := by
  rw [selectedCellProjection_apply hq, inner_smul_right]

theorem fullCellSymbol_selected_pairing {h z σ : ℝ} (D : Auxiliary.Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) {q : Momentum}
    (hq : ‖q‖ ≤ separatedRadius) (hchart : q ∈ physicalChart)
    (hne : dielectricBand q - ((z+σ : ℝ) : ℂ) ≠ 0) (g f : CellFieldL2) :
    inner ℂ g (fullCellSymbol z σ q f) =
      (selectedCellFunctional q f * inner ℂ g (selectedCellVector q)) /
        (dielectricBand q - ((z+σ : ℝ) : ℂ)) +
      inner ℂ g (separatedCellSymbol z σ q f) := by
  rw [fullCellSymbol_pole_formula D hσ0 hσ hq hne, add_apply,
    smul_apply, inner_add_right, inner_smul_right, selectedCellProjection_pairing hchart]
  congr 1
  ring

#print axioms fullCellSymbol_selected_pairing

end Maxwell.Continuum.CellGauge
