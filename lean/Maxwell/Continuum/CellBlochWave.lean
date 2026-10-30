import Maxwell.Continuum.CellSelectedRankOne
import Maxwell.Continuum.CellSpatialFourier
import Maxwell.Continuum.CellBandFourierPairing

/-! The gauged cell Fourier vector is the literal physical Bloch wave,
including the fixed imaginary phase of the chosen real corner mode. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.CellGauge

open Complex FreeFiber PeriodicBand FiberNormalization CellBandFourier MeasureTheory

attribute [local irreducible] normalizedFiberVector

theorem spatialPhase_corner (x : Space) : spatialPhase CellGauge.corner x = carrier x := by
  simp only [spatialPhase, CellGauge.corner, realMomentum, carrier,
    Complex.ofReal_div, Complex.ofReal_ofNat, Fin.sum_univ_three]
  congr 1
  push_cast
  ring

theorem gauged_unitary_ae (q : Momentum) (u : FiberSpace)
    (hu : Summable (fun ν => ‖u ν‖)) (j : Fin 3) :
    antiGauge q (CellFourier.unitary u) j =ᵐ[torusMeasure] fun t =>
      blochField q u (spatialEquiv t).val j := by
  rw [antiGauge_eq, CellFourier.unitary_eq_cellL2 u hu]
  filter_upwards [gauge_ae (q+CellGauge.corner) (cellL2 u) j, scalarCellL2_ae u j] with t hg hu
  rw [hg]
  change coefficient (q+CellGauge.corner) (cellPoint t) * scalarCellL2 u j t = _
  rw [hu, gaugeCoefficient_spatial, spatialPhase_add, spatialPhase_corner]
  simp only [blochField, antiperiodicField, periodicField,
    PiLp.smul_apply, smul_eq_mul, torusPoint_spatialEquiv]
  ring

def selectedCellWave (q : Momentum) : CellFieldL2 := I • selectedCellVector q

def physicalSelectedWave (q : Momentum) (x : Space) : Polarization :=
  spatialPhase q x • cellEigenfunction (unscale q) x

theorem physicalSelectedWave_eq (q : Momentum) (x : Space) :
    physicalSelectedWave q x = I • blochField q (normalizedFiberVector (unscale q)) x := by
  unfold physicalSelectedWave cellEigenfunction blochField
  exact smul_comm _ _ _

theorem selectedCellWave_ae {q : Momentum} (hq : q ∈ physicalChart) (j : Fin 3) :
    selectedCellWave q j =ᵐ[torusMeasure] fun t => physicalSelectedWave q (spatialEquiv t).val j := by
  have hv := gauged_unitary_ae q (normalizedFiberVector (unscale q))
    (normalizedFiberVector_fourier_l1 (unscale_mem_chart hq)).1 j
  filter_upwards [Lp.coeFn_smul I (selectedCellVector q j), hv] with t hsm hv
  change (I • selectedCellVector q j) t = _
  rw [hsm]
  change I * antiGauge q (CellFourier.unitary (normalizedFiberVector (unscale q))) j t = _
  rw [hv, physicalSelectedWave_eq]
  rfl

#print axioms selectedCellWave_ae

end Maxwell.Continuum.CellGauge
