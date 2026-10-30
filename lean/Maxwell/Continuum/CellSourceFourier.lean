import Maxwell.Continuum.CellSourceBloch

/-! Actual whole-space Fourier formula for a translated compact-source
matrix element of the continuum Maxwell cutoff resolvent. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.CellGauge

open Complex FreeFiber PeriodicBand CellBandFourier EffectiveMass Bloch Auxiliary MeasureTheory OperatorFourier

attribute [local irreducible] Auxiliary.resolvent fullCellSymbol

theorem cellPacket_cutoff_pairing (h z σ : ℝ) (u v : FieldL2) (q : QuasiCell) :
    inner ℂ (cellSourcePacket h u (quasiMomentum q))
      (cutoffFullCellSymbol z σ q.val (cellSourcePacket h v (quasiMomentum q))) =
        (cutoff q.val : ℂ)*cellSourcePairing h u v (fullCellSymbol z σ) (realMomentumMap q.val) := by
  rw [cellSourcePairing_eq_inner]
  change inner ℂ (cellSourcePacket h u (quasiMomentum q))
    (((cutoff q.val : ℂ) • fullCellSymbol z σ (quasiMomentum q)) (cellSourcePacket h v (quasiMomentum q))) =
      (cutoff q.val : ℂ)*inner ℂ (cellSourcePacket h u (star (quasiMomentum q)))
        (fullCellSymbol z σ (quasiMomentum q) (cellSourcePacket h v (quasiMomentum q)))
  rw [quasiMomentum_star, smul_apply, inner_smul_right]

theorem source_resolvent_fourier_integral {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (a : Bloch.Alias) (u v : FieldL2) :
    inner ℂ (sourceMode h u)
      (resolvent D hσ0 hσ (fieldTranslation (-latticeShift a) (sourceMode h v))) =
      ((64*blochDensity : ℝ) : ℂ)*carrier (latticeShift a)*
        ∫ q : Space, OperatorFourier.angularPhase q (latticeShift a)*(cutoff q : ℂ)*
          cellSourcePairing h u v (fullCellSymbol z σ) (realMomentumMap q) := by
  rw [source_resolvent_pairing D hσ0 hσ]
  simp_rw [cellPacket_cutoff_pairing, latticePhase_angular, carrier_neg_lattice]
  have he : (∫ q : QuasiCell,
      (carrier (latticeShift a)*Complex.exp ((-inner ℝ q.val (latticeShift a) : ℝ)*Complex.I))*
        ((cutoff q.val : ℂ)*cellSourcePairing h u v (fullCellSymbol z σ) (realMomentumMap q.val)) ∂quasiMeasure) =
      carrier (latticeShift a)*∫ q : QuasiCell,
        OperatorFourier.angularPhase q.val (latticeShift a)*(cutoff q.val : ℂ)*
          cellSourcePairing h u v (fullCellSymbol z σ) (realMomentumMap q.val) ∂quasiMeasure := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun q => by unfold OperatorFourier.angularPhase; ring
  rw [he]
  have hz (q : Space) (hq : q ∉ quasiCell) : OperatorFourier.angularPhase q (latticeShift a)*(cutoff q : ℂ)*
      cellSourcePairing h u v (fullCellSymbol z σ) (realMomentumMap q) = 0 := by
    rw [cutoff_zero_outside_quasi hq, Complex.ofReal_zero, mul_zero, zero_mul]
  rw [quasi_integral_supported _ hz, Complex.real_smul]
  push_cast
  ring

#print axioms source_resolvent_fourier_integral

end Maxwell.Continuum.CellGauge
