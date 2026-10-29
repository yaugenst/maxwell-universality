import Maxwell.Continuum.EffectiveMassEnvelope
import Maxwell.Continuum.FourierConjugation

/-! The literal reference spatial envelope is real in the same physical
conjugation used for the Maxwell resolvent. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory CellBandFourier PeriodicBand

theorem cellEigenfunction_zero_real (x : Space) (j : Fin 3) :
    star (cellEigenfunction 0 x j) = cellEigenfunction 0 x j := by
  have he := cellEigenfunction_real_imaginary chart_zero (by simp) x
  exact congrArg (fun v : FreeFiber.Polarization => v j) he

theorem envelope_conjugation {h : ℝ} (hh : 0 < h) (f : ScalarL2) :
    fieldConjugation (envelopeOperator hh f) = envelopeOperator hh (scalarConjugation f) := by
  apply PiLp.ext
  intro j
  apply Lp.ext
  have hs := L2Dilation.inverse_ae (inv_pos.mpr hh) (scalarConjugation_ae f)
  filter_upwards [scalarConjugation_ae (envelopeOperator hh f j),
    envelopeOperator_ae hh f j, envelopeOperator_ae hh (scalarConjugation f) j, hs]
    with x hc he ho hsx
  change scalarConjugation (envelopeOperator hh f j) x = envelopeOperator hh (scalarConjugation f) j x
  rw [hc, he, ho]
  simp only [inv_inv] at hsx
  rw [hsx]
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
  rw [← Complex.star_def, cellEigenfunction_zero_real]
  ring

theorem scalarWell_mode_real : scalarConjugation Well.topVector = Well.topVector := by
  apply Lp.ext
  filter_upwards [scalarConjugation_ae Well.topVector, Well.topVector_nonnegative] with x hc hr
  rw [hc, hr.1, Complex.star_def, Complex.conj_ofReal]

theorem referencePhysicalMode_real {h : ℝ} (hh : 0 < h) :
    fieldConjugation (referencePhysicalMode hh) = referencePhysicalMode hh := by
  change fieldConjugation (envelopeOperator hh Well.topVector) = _
  rw [envelope_conjugation, scalarWell_mode_real]
  rfl

end Maxwell.Continuum.EffectiveMass
