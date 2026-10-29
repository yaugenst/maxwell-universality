import Maxwell.Continuum.PeriodicBand
import Maxwell.Continuum.RankOneBandWideKernel
import Maxwell.Continuum.ClusterComplementResolventAnalytic

/-! Full bounded-resolvent exclusion on the wider scaled energy disk.
The band remains the root constructed on radius `1/100`; the larger
`1/50` exclusion window leaves a literal `ρ/100` gap around that root. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber ClusterComplement FiberAnalytic PeriodicPerturbation CornerBridge Metric Set

theorem wide_energy_norm_le {e : ℂ}
    (he : ‖e - (Corner.lambdaStar : ℂ)‖ ≤ 1 / 50) : ‖e‖ ≤ 3 := by
  have hc : ‖(Corner.lambdaStar : ℂ)‖ ≤ 5 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Corner.lambdaStar_pos]
    exact lambdaStar_le
  have hsum := norm_add_le (e - (Corner.lambdaStar : ℂ)) (Corner.lambdaStar : ℂ)
  rw [sub_add_cancel] at hsum
  linarith

theorem chart_wide_energy_inBox {t : Momentum} {e : ℂ}
    (ht : t ∈ chart) (he : ‖e - (Corner.lambdaStar : ℂ)‖ ≤ 1 / 50) : InBox (t, e) :=
  ⟨chart_closed_bounds ht, (wide_energy_norm_le he).trans (by norm_num)⟩

theorem schur_nonzero_iff_scaledBand_wide {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : ‖e - (Corner.lambdaStar : ℂ)‖ ≤ 1 / 50) :
    (∃ x : clusterSpace, x ≠ 0 ∧ finiteSchurExtension (t, e) x = 0) ↔ e = scaledBand t := by
  rw [finiteSchurExtension_expansion]
  exact actualCornerData.kernel_nonzero_iff_bandRoot_wide perturbationData t ht e he
    (perturbation_norm_le (t, e) (chart_wide_energy_inBox ht he))

/-- This excludes genuine full-fiber eigenvalues on the larger disk. -/
theorem actual_nonzero_iff_scaledBand_wide {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : ‖e - (Corner.lambdaStar : ℂ)‖ ≤ 1 / 50) :
    (∃ u : FiberSpace, u ≠ 0 ∧
      (u, 0) ∈ (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude).graph) ↔
      e = scaledBand t :=
  (schurExtension_nonzero_iff_actual t e (chart_closed_bounds ht)
    (chart_wide_energy_inBox ht he).2).symm.trans (schur_nonzero_iff_scaledBand_wide ht he)

theorem finiteSchurExtension_isUnit_wide {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : ‖e - (Corner.lambdaStar : ℂ)‖ ≤ 1 / 50) (hne : e ≠ scaledBand t) :
    IsUnit (finiteSchurExtension (t, e)) := by
  have hinj : Function.Injective (finiteSchurExtension (t, e)).toLinearMap := by
    intro x y hxy
    by_contra hne'
    apply hne
    apply (schur_nonzero_iff_scaledBand_wide ht he).mp
    refine ⟨x - y, sub_ne_zero.mpr hne', ?_⟩
    rw [map_sub]
    exact sub_eq_zero.mpr hxy
  exact ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

/-- The inverse acts on the entire ambient ℓ² space and has range in the
literal maximal domain of the complex-momentum material fiber. -/
def inverseAwayFromBand {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : ‖e - (Corner.lambdaStar : ℂ)‖ ≤ 1 / 50) (hne : e ≠ scaledBand t) :
    SelfAdjointResolvent.BoundedInverse
      (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude) :=
  inverseFromSchur t e (chart_wide_energy_inBox ht he).1 (chart_wide_energy_inBox ht he).2
    (by rw [← finiteSchurExtension_eq (t, e) (chart_wide_energy_inBox ht he)]
        exact finiteSchurExtension_isUnit_wide ht he hne)

theorem fullResolventExtension_eq_inverseAwayFromBand {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : ‖e - (Corner.lambdaStar : ℂ)‖ ≤ 1 / 50) (hne : e ≠ scaledBand t) :
    fullResolventExtension (t, e) = (inverseAwayFromBand ht he hne).map :=
  fullResolventExtension_eq (t, e) (chart_wide_energy_inBox ht he)

theorem fullResolventExtension_analytic_wide {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : ‖e - (Corner.lambdaStar : ℂ)‖ ≤ 1 / 50) (hne : e ≠ scaledBand t) :
    AnalyticAt ℂ fullResolventExtension (t, e) :=
  analyticAt_fullResolventExtension (t, e) (chart_wide_energy_inBox ht he)
    (finiteSchurExtension_isUnit_wide ht he hne)

theorem energy_near_band_in_wide {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : ‖e - scaledBand t‖ ≤ 1 / 100) : ‖e - (Corner.lambdaStar : ℂ)‖ ≤ 1 / 50 := by
  have h := norm_add_le (e - scaledBand t) (scaledBand t - (Corner.lambdaStar : ℂ))
  rw [sub_add_sub_cancel] at h
  linarith [scaledBand_center_bound ht]

/-- The complete inverse exists at every other energy within scaled
distance `1/100` of the actual band, including the boundary circle. -/
theorem boundedInverse_near_band {t : Momentum} (ht : t ∈ chart) {e : ℂ}
    (he : ‖e - scaledBand t‖ ≤ 1 / 100) (hne : e ≠ scaledBand t) :
    Nonempty (SelfAdjointResolvent.BoundedInverse
      (materialFiber (scaledMomentum t) (totalEnergy e) backgroundAmplitude)) :=
  ⟨inverseAwayFromBand ht (energy_near_band_in_wide ht he) hne⟩

end Maxwell.Continuum.PeriodicBand
