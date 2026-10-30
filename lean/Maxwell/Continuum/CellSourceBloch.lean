import Maxwell.Continuum.CellSourcePairing

/-! Exact Bloch representation of the physical compact source and its
translated resolvent matrix element. This retains the full Fourier basis. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.CellGauge

open Complex FreeFiber PeriodicBand CellBandFourier EffectiveMass Bloch Auxiliary MeasureTheory

attribute [local irreducible] Bloch.unitary Auxiliary.resolvent

theorem quasiMomentum_star (q : QuasiCell) : star (quasiMomentum q) = quasiMomentum q := by
  ext j
  simp only [quasiMomentum, Pi.star_apply, Complex.star_def, Complex.conj_ofReal]

theorem latticePhase_eq_sourceLatticeFactor (a : Bloch.Alias) (q : QuasiCell) :
    latticePhase a q = sourceLatticeFactor (-quasiMomentum q) a := by
  rw [latticePhase_angular, carrier_neg_lattice, sourceLatticeFactor, mul_comm]
  congr 1
  unfold spatialPhase
  congr 1
  simp only [quasiMomentum, Pi.neg_apply, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct, star_trivial, Fin.sum_univ_three, Complex.ofReal_neg,
    Complex.ofReal_add, Complex.ofReal_mul]
  ring

theorem sourceMode_eq_cell_sum {h : ℝ} (hh : 0 < h) (u : FieldL2) :
    sourceMode h u = ∑ a ∈ ballCells h⁻¹,
      embedLatticeCell a (restrictLatticeCell a (sourceMode h u)) := by
  have he := congrArg (fun T : FieldL2 →L[ℂ] FieldL2 => T u)
    (familyProjection_Qh (inv_pos.mpr hh))
  simp only [ContinuousLinearMap.comp_apply, inv_inv] at he
  change familyProjection (ballCells h⁻¹) (sourceMode h u) = sourceMode h u at he
  rw [familyProjection_apply] at he
  exact he.symm

theorem unitary_sourceMode {h : ℝ} (hh : 0 < h) (u : FieldL2) :
    unitary (sourceMode h u) =ᵐ[quasiMeasure] fun q =>
      (8 : ℂ) • CellFourier.unitary.symm
        (antiUngauge (quasiMomentum q) (cellSourcePacket h u (quasiMomentum q))) := by
  have he := congrArg unitary (sourceMode_eq_cell_sum hh u)
  rw [map_sum] at he
  rw [he]
  filter_upwards [Lp.coeFn_finsetSum (ballCells h⁻¹) (fun a =>
    unitary (embedLatticeCell a (restrictLatticeCell a (sourceMode h u)))),
    ae_all_iff.mpr (fun a : Bloch.Alias =>
      unitary_embedLatticeCell a (restrictLatticeCell a (sourceMode h u)))] with q hs hc
  rw [hs]
  simp only [Finset.sum_apply, hc, latticePhase_eq_sourceLatticeFactor,
    cellSourcePacket, map_sum, map_smul, Finset.smul_sum, smul_smul]

theorem source_resolvent_pairing {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4/64) (a : Bloch.Alias) (u v : FieldL2) :
    inner ℂ (sourceMode h u)
      (resolvent D hσ0 hσ (fieldTranslation (-latticeShift a) (sourceMode h v))) =
      (64 : ℂ)*∫ q : QuasiCell, latticePhase a q *
        inner ℂ (cellSourcePacket h u (quasiMomentum q))
          (cutoffFullCellSymbol z σ q.val (cellSourcePacket h v (quasiMomentum q))) ∂quasiMeasure := by
  rw [← unitary_inner, L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [unitary_sourceMode D.h_pos u, unitary_sourceMode D.h_pos v,
    unitary_fieldTranslation_ae (-latticeShift a) (sourceMode h v),
    resolvent_ae D hσ0 hσ (fieldTranslation (-latticeShift a) (sourceMode h v))]
      with q hu hv ht hR
  rw [hu, hR, ht, hv, fiberTranslation_lattice, map_smul, map_smul,
    inner_smul_left, inner_smul_right, inner_smul_right, cutoffFullCellSymbol_pairing]
  simp only [map_ofNat]
  ring

#print axioms unitary_sourceMode
#print axioms source_resolvent_pairing

end Maxwell.Continuum.CellGauge
