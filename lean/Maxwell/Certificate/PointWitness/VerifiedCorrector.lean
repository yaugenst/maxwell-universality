import Maxwell.Certificate.PointWitness.CorrectorConstruction
import Maxwell.Certificate.CorrectorWitness.SavedComputed

/-! The actual finite saved-corrector checks discharge every replacement
premise. Only the named point spectral-isolation input remains. -/

namespace Maxwell.Certificate.PointWitness

open Maxwell.Spectral

noncomputable section

theorem pointSavedCorrector_odd (q : PeriodicYee.Momentum) :
    HasParity pointInversion (-1) (CorrectorWitness.savedCorrector q) := by
  intro x
  simpa only [pointInversion, neg_one_smul] using CorrectorWitness.savedCorrector_odd q x

theorem pointCorrector_saved_close (hgap : PointClusterComplementGap)
    (q : PeriodicYee.Momentum) :
    ‖pointCorrector hgap q - CorrectorWitness.savedCorrector q‖ ≤
      ((1 : ℝ) / 2^24) * YeeTaylor.radius q :=
  pointCorrector_error_of_saved_bounds hgap q (CorrectorWitness.savedCorrector q)
    (pointSavedCorrector_odd q) (CorrectorWitness.savedCorrector_norm_le q)
    (CorrectorWitness.savedCorrector_residual_bound q)

/-- The manuscript exact-corrector norm follows from literal finite data and
the proved energy-centered reduced inverse. -/
theorem pointCorrector_norm_le (hgap : PointClusterComplementGap)
    (q : PeriodicYee.Momentum) : ‖pointCorrector hgap q‖ ≤ 3 * YeeTaylor.radius q :=
  pointCorrector_norm_of_saved_bounds hgap q (CorrectorWitness.savedCorrector q)
    (pointSavedCorrector_odd q) (CorrectorWitness.savedCorrector_norm_le q)
    (CorrectorWitness.savedCorrector_residual_bound q)

end
end Maxwell.Certificate.PointWitness
