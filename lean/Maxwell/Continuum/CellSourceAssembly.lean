import Maxwell.Continuum.CellSourcePacket

/-! The positive source numerator and the finite physical-cell source
packet have exactly the same spatial integral, including normalization. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.CellGauge

open Complex FreeFiber PeriodicBand FiberNormalization CellBandFourier MeasureTheory EffectiveMass Bloch Set

theorem integral_eq_sum_cells (F : Space → ℂ) (s : Finset Bloch.Alias) (hF : Integrable F)
    (hs : ∀ᵐ x ∂volume, cellIndex x ∉ s → F x = 0) :
    (∫ x, F x) = ∑ a ∈ s, ∫ x in spatialBox a, F x := by
  have hzero : ∀ᵐ x ∂volume, x ∉ ⋃ a ∈ s, spatialBox a → F x = 0 := by
    filter_upwards [hs] with x hx hnot
    apply hx
    intro hm
    apply hnot
    exact mem_iUnion.mpr ⟨cellIndex x, mem_iUnion.mpr ⟨hm, mem_spatialBox_index x⟩⟩
  rw [← setIntegral_eq_integral_of_ae_compl_eq_zero hzero]
  exact integral_biUnion_finset s (fun a _ => spatialBox_measurable a)
    (fun _ _ _ _ hab => spatialBox_disjoint hab) (fun _ _ => hF.integrableOn)

theorem sourceFactor_cell_sum {h : ℝ} (hh : 0 < h) (u : FieldL2) {q : Momentum}
    (hq : q ∈ physicalChart) :
    sourceFactor h u q = ((8*fourierNormalization : ℝ) : ℂ) *
      ∑ a ∈ ballCells h⁻¹, sourceLatticeFactor q a *
        cellSourceFunctional (-q) (restrictLatticeCell a (sourceMode h u)) := by
  have hz : ∀ᵐ x ∂volume, cellIndex x ∉ ballCells h⁻¹ → sourceIntegrand h u q x = 0 := by
    filter_upwards [sourceValue_supported hh u] with x hx hnot
    have hn : h⁻¹ ≤ ‖x‖ := by
      by_contra hn
      exact hnot (cellIndex_mem_ballCells (le_of_lt (lt_of_not_ge hn)))
    rw [sourceIntegrand, hx hn, map_zero, mul_zero]
  rw [sourceFactor, integral_eq_sum_cells _ _ (sourceIntegrand_integrable hh u hq) hz]
  have he (a : Bloch.Alias) : (∫ x in spatialBox a, sourceIntegrand h u q x) =
      (8 : ℂ)*sourceLatticeFactor q a*cellSourceFunctional (-q) (restrictLatticeCell a (sourceMode h u)) := by
    simp_rw [sourceIntegrand_wave]
    change (∫ x in spatialBox a, bilinear (physicalSelectedWave q x) (fieldValue (sourceMode h u) x)) = _
    simpa only [neg_neg] using cellSourceFunctional_lattice (-q) a (sourceMode h u)
  simp_rw [he]
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem cellSourceFunctional_packet {q : Momentum} (hq : q ∈ physicalChart)
    (h : ℝ) (u : FieldL2) :
    cellSourceFunctional q (cellSourcePacket h u q) =
      ∑ a ∈ ballCells h⁻¹, sourceLatticeFactor (-q) a *
        cellSourceFunctional q (restrictLatticeCell a (sourceMode h u)) := by
  rw [cellSourceFunctional_eq hq, cellSourcePacket, map_sum]
  simp_rw [map_smul, smul_eq_mul, cellSourceFunctional_eq hq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem sourceFactor_eq_cellPacket {h : ℝ} (hh : 0 < h) (u : FieldL2) {q : Momentum}
    (hq : q ∈ physicalChart) :
    sourceFactor h u (-q) = ((8*fourierNormalization : ℝ) : ℂ) *
      cellSourceFunctional q (cellSourcePacket h u q) := by
  rw [sourceFactor_cell_sum hh u (source_physicalChart_neg hq), cellSourceFunctional_packet hq]
  simp only [neg_neg]

#print axioms sourceFactor_eq_cellPacket

end Maxwell.Continuum.CellGauge
