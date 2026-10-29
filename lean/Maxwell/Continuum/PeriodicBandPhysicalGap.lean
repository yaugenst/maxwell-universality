import Maxwell.Continuum.PeriodicBandSeparation

/-! The spectral exclusion in physical energy units. The radius is
literally `ρ/100`, centered at the constructed band, and every excluded
energy has a bounded inverse on the full maximal fiber domain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber ClusterComplement FiberAnalytic

def physicalBand (t : Momentum) : ℂ := totalEnergy (scaledBand t)

def scaledEnergy (E : ℂ) : ℂ :=
  (E - ((3 * Real.pi ^ 2 / 4 : ℝ) : ℂ)) / (backgroundAmplitude : ℂ)

theorem totalEnergy_sub (e f : ℂ) :
    totalEnergy e - totalEnergy f = (backgroundAmplitude : ℂ) * (e - f) := by
  unfold totalEnergy
  ring

theorem totalEnergy_sub_norm (e f : ℂ) :
    ‖totalEnergy e - totalEnergy f‖ = backgroundAmplitude * ‖e - f‖ := by
  rw [totalEnergy_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos backgroundAmplitude_pos]

theorem totalEnergy_scaledEnergy (E : ℂ) : totalEnergy (scaledEnergy E) = E := by
  have hρ : (backgroundAmplitude : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr backgroundAmplitude_pos.ne'
  unfold totalEnergy scaledEnergy
  field_simp
  ring

theorem scaledEnergy_near_physicalBand {t : Momentum} {E : ℂ}
    (hE : ‖E - physicalBand t‖ ≤ backgroundAmplitude / 100) :
    ‖scaledEnergy E - scaledBand t‖ ≤ 1 / 100 := by
  have h := totalEnergy_sub_norm (scaledEnergy E) (scaledBand t)
  rw [totalEnergy_scaledEnergy] at h
  change ‖E - totalEnergy (scaledBand t)‖ ≤ _ at hE
  rw [h] at hE
  nlinarith [backgroundAmplitude_pos]

theorem scaledEnergy_ne_band {t : Momentum} {E : ℂ} (hne : E ≠ physicalBand t) :
    scaledEnergy E ≠ scaledBand t := by
  intro h
  apply hne
  exact (totalEnergy_scaledEnergy E).symm.trans (congrArg totalEnergy h)

/-- No other physical spectral point lies within `ρ/100` of this band:
this constructs a complete two-sided inverse, not merely a trivial kernel. -/
def inverseNearPhysicalBand {t : Momentum} (ht : t ∈ chart) {E : ℂ}
    (hE : ‖E - physicalBand t‖ ≤ backgroundAmplitude / 100) (hne : E ≠ physicalBand t) :
    SelfAdjointResolvent.BoundedInverse (materialFiber (scaledMomentum t) E backgroundAmplitude) := by
  have R := inverseAwayFromBand ht
    (energy_near_band_in_wide ht (scaledEnergy_near_physicalBand hE)) (scaledEnergy_ne_band hne)
  rw [totalEnergy_scaledEnergy] at R
  exact R

theorem physical_gap_boundedInverse {t : Momentum} (ht : t ∈ chart) {E : ℂ}
    (hE : ‖E - physicalBand t‖ ≤ backgroundAmplitude / 100) (hne : E ≠ physicalBand t) :
    Nonempty (SelfAdjointResolvent.BoundedInverse
      (materialFiber (scaledMomentum t) E backgroundAmplitude)) :=
  ⟨inverseNearPhysicalBand ht hE hne⟩

theorem physical_band_kernel_finrank {t : Momentum} (ht : t ∈ chart) :
    Module.finrank ℂ (ActualKernel t (scaledBand t)) = 1 := actual_band_kernel_finrank ht

end Maxwell.Continuum.PeriodicBand
