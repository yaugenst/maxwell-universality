import Maxwell.Continuum.CellSpatialTranslation
import Maxwell.Continuum.CellGaugeUnitary
import Maxwell.Continuum.CellSeparatedDecay
import Maxwell.Continuum.SeparatedPhysicalOperator

/-! Exact physical translated-cell matrix elements of the actual separated
operator. The complete L² cell gauge is included on both sides. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellGauge

open FreeFiber FiberAnalytic CellBandFourier Auxiliary Bloch MeasureTheory

attribute [local irreducible] separatedSymbol cutoffSeparatedSymbol cutoffCellSymbol
  physicalSeparated Bloch.unitary

theorem cutoffCellSymbol_apply (z σ : ℝ) (q : Space) (f : CellFieldL2) :
    cutoffCellSymbol z σ q f = antiGauge (realMomentumMap q)
      (conjugate (cutoffSeparatedSymbol z σ q) (antiUngauge (realMomentumMap q) f)) := by
  unfold cutoffCellSymbol cutoffSymbol realSymbol separatedCellSymbol cutoffSeparatedSymbol realSeparatedSymbol
  change (cutoff q : ℂ) • antiGauge (realMomentumMap q)
      (conjugate (separatedSymbol z σ (realMomentumMap q)) (antiUngauge (realMomentumMap q) f)) = _
  rw [map_smul, smul_apply, map_smul]

theorem cutoffCellSymbol_pairing (z σ : ℝ) (q : QuasiCell) (g f : CellFieldL2) :
    inner ℂ (CellFourier.unitary.symm (antiUngauge (quasiMomentum q) g))
      (cutoffSeparatedSymbol z σ q.val
        (CellFourier.unitary.symm (antiUngauge (quasiMomentum q) f))) =
      inner ℂ g (cutoffCellSymbol z σ q.val f) := by
  rw [cutoffCellSymbol_apply]
  exact gauged_inner (fun j => q.val j) (cutoffSeparatedSymbol z σ q.val) g f

theorem physicalSeparated_cell_pairing {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) (a b : Bloch.Alias) (g f : CellFieldL2) :
    inner ℂ (embedLatticeCell a g) (physicalSeparated D hσ0 hσ (embedLatticeCell b f)) =
      (64 : ℂ) * ∫ q : QuasiCell, (star (latticePhase a q) * latticePhase b q) *
        inner ℂ g (cutoffCellSymbol z σ q.val f) ∂quasiMeasure := by
  rw [← unitary_inner, L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [unitary_embedLatticeCell a g, unitary_embedLatticeCell b f,
    physicalSeparated_ae D hσ0 hσ (embedLatticeCell b f)] with q hg hf hR
  rw [hg, hR, hf, map_smul, inner_smul_left, inner_smul_right, cutoffCellSymbol_pairing]
  simp only [map_mul, map_ofNat, starRingEnd_apply]
  ring

#print axioms cutoffCellSymbol_pairing
#print axioms physicalSeparated_cell_pairing

end Maxwell.Continuum.CellGauge
