import Maxwell.Continuum.CellSourceReality
import Maxwell.Continuum.CellSourceAnalytic
import Maxwell.Continuum.CellSourcePacketScaled
import Maxwell.Continuum.EffectiveMassScalingIntegral
import Maxwell.Continuum.FullCellKernel

/-! The literal source-contracted cell symbol is holomorphic. Its
selected part has exactly the positive continuum source numerator. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.CellGauge

open Complex FreeFiber PeriodicBand FiberNormalization CellBandFourier EffectiveMass Bloch Auxiliary

def cellSourcePairing (h : ℝ) (u v : FieldL2) (Y : Momentum → CellMap) (q : Momentum) : ℂ :=
  ∑ a ∈ ballCells h⁻¹, sourceLatticeFactor q a *
    inner ℂ (restrictLatticeCell a (sourceMode h u)) (Y q (cellSourcePacket h v q))

theorem cellSourcePairing_eq_inner (h : ℝ) (u v : FieldL2) (Y : Momentum → CellMap) (q : Momentum) :
    cellSourcePairing h u v Y q =
      inner ℂ (cellSourcePacket h u (star q)) (Y q (cellSourcePacket h v q)) := by
  rw [cellSourcePacket, sum_inner]
  simp only [inner_smul_left, starRingEnd_apply, sourceLatticeFactor_star, cellSourcePairing]

theorem cellSourcePairing_analytic (h : ℝ) (u v : FieldL2) {Y : Momentum → CellMap} {q : Momentum}
    (hY : AnalyticAt ℂ Y q) : AnalyticAt ℂ (cellSourcePairing h u v Y) q := by
  apply Finset.analyticAt_fun_sum
  intro a _
  apply (sourceLatticeFactor_analytic a q).mul
  have ha := (hY.contDiffAt.clm_apply (cellSourcePacket_analytic h v q).contDiffAt).analyticAt
  exact ((innerSL ℂ (restrictLatticeCell a (sourceMode h u))).analyticAt _).comp
    (f := fun p => Y p (cellSourcePacket h v p)) ha

theorem cellSourcePairing_selected {h : ℝ} {u : FieldL2} (hu : fieldConjugation u = u)
    {q : Momentum} (hq : q ∈ physicalChart) :
    cellSourcePairing h u u selectedCellProjection q =
      cellSourceFunctional q (cellSourcePacket h u q)*
        cellSourceFunctional (-q) (cellSourcePacket h u (-q)) := by
  rw [cellSourcePairing_eq_inner, selectedCellProjection_physical hq, inner_smul_right,
    cellSourcePacket_wave_pairing hu hq]

theorem cellSourcePairing_selected_numerator {h : ℝ} (hh : 0 < h) {u : FieldL2}
    (hu : fieldConjugation u = u) {q : Momentum} (hq : q ∈ physicalChart) :
    ((8*fourierNormalization : ℝ) : ℂ)^2 * cellSourcePairing h u u selectedCellProjection q =
      sourceFactor h u q*sourceFactor h u (-q) := by
  have hp := sourceFactor_eq_cellPacket hh u (source_physicalChart_neg hq)
  simp only [neg_neg] at hp
  rw [hp, sourceFactor_eq_cellPacket hh u hq, cellSourcePairing_selected hu hq]
  ring

theorem cellSource_normalization : ((64*blochDensity : ℝ) : ℂ) =
    ((8*fourierNormalization : ℝ) : ℂ)^2 := by
  have he : fourierNormalization^2 = blochDensity := fourierNormalization_square
  rw [← Complex.ofReal_pow]
  congr 1
  rw [mul_pow, he]
  norm_num

theorem cellSourcePairing_full_pole {h z : ℝ} (D : Auxiliary.Calibration h z)
    {u : FieldL2} (hu : fieldConjugation u = u) {q : Momentum}
    (hq : ‖q‖ ≤ separatedRadius) (hchart : q ∈ physicalChart)
    (hne : dielectricBand q - (z : ℂ) ≠ 0) :
    ((64*blochDensity : ℝ) : ℂ)*cellSourcePairing h u u (fullCellSymbol z 0) q =
      sourceFactor h u q*sourceFactor h u (-q)/(dielectricBand q-(z : ℂ))+
      ((64*blochDensity : ℝ) : ℂ)*cellSourcePairing h u u (separatedCellSymbol z 0) q := by
  have hn : dielectricBand q-((z+(0 : ℝ) : ℝ) : ℂ) ≠ 0 := by simpa only [add_zero] using hne
  have hs : cellSourcePairing h u u (fullCellSymbol z 0) q =
      (dielectricBand q-(z : ℂ))⁻¹ * cellSourcePairing h u u selectedCellProjection q+
        cellSourcePairing h u u (separatedCellSymbol z 0) q := by
    simp only [cellSourcePairing_eq_inner]
    rw [fullCellSymbol_pole_formula D le_rfl (by positivity) hq hn,
      add_apply, smul_apply, inner_add_right, inner_smul_right, add_zero]
  rw [hs, mul_add, cellSource_normalization]
  have he := cellSourcePairing_selected_numerator D.h_pos hu hchart
  calc
    _ = (((8*fourierNormalization : ℝ) : ℂ)^2*cellSourcePairing h u u selectedCellProjection q)/
        (dielectricBand q-(z : ℂ))+
        ((8*fourierNormalization : ℝ) : ℂ)^2*cellSourcePairing h u u (separatedCellSymbol z 0) q := by ring
    _ = _ := by rw [he]

#print axioms cellSourcePairing_analytic
#print axioms cellSourcePairing_full_pole

end Maxwell.Continuum.CellGauge
