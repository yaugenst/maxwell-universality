import Maxwell.Continuum.CalibrationSupercellRange

/-! The exact supercell range also contains the translated well used
for coupling calibration. -/

noncomputable section

namespace Maxwell.Continuum.Calibration.Supercell

open FreeFiber CellGauge CellBandFourier PeriodicSampling Bloch EffectiveMass

variable (M : ℕ) [NeZero M]

theorem wellCells_subset_represented {L : ℝ} (hL : 1≤L) (k : Bloch.Alias)
    (hM : 16*(L+(imageRadius k : ℝ)+1)≤(M : ℝ)) :
    wellCells L k⊆representedCells M := by
  intro a ha
  exact Finset.mem_map.mpr ⟨Product.frequency M a,Finset.mem_univ _,
    twoWellCells_representative M hL k hM (Finset.mem_union_right _ ha)⟩

theorem embedding_range_translatedQh {L : ℝ} (hL : 1≤L) (k : Bloch.Alias)
    (hM : 16*(L+(imageRadius k : ℝ)+1)≤(M : ℝ)) (f : FieldL2) :
    embedding M ((embedding M).toContinuousLinearMap.adjoint
      (fieldTranslation (-latticeShift k) (Qh L⁻¹ f)))=
      fieldTranslation (-latticeShift k) (Qh L⁻¹ f) := by
  rw [embedding_range_projection]
  have hi := familyProjection_translatedQh (by linarith : 0<L) k f
  have h := familyProjection_subset_apply (wellCells_subset_represented M hL k hM)
    (fieldTranslation (-latticeShift k) (Qh L⁻¹ f))
  rw [hi] at h
  exact h

#print axioms embedding_range_translatedQh

end Maxwell.Continuum.Calibration.Supercell
