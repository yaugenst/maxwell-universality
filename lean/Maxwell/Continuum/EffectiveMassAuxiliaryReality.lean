import Maxwell.Continuum.EffectiveMassAuxiliaryTranslation

/-! Physical reality and actual support of the auxiliary well operator. -/

noncomputable section

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory Auxiliary

theorem Qh_conjugation (h : ℝ) (f : FieldL2) :
    fieldConjugation (Qh h f) = Qh h (fieldConjugation f) := by
  apply PiLp.ext
  intro j
  apply Lp.ext
  filter_upwards [scalarConjugation_ae (Qh h f j), Qh_ae h f j,
    Qh_ae h (fieldConjugation f) j, scalarConjugation_ae (f j)] with x hc hq hqc hf
  change scalarConjugation (Qh h f j) x = Qh h (fieldConjugation f) j x
  rw [hc, hq, hqc, fieldConjugation_apply, hf, star_mul', Complex.star_def,
    Complex.conj_ofReal]

theorem Sh_conjugation {h z : ℝ} (D : Calibration h z) (f : FieldL2) :
    fieldConjugation (Sh D f) = Sh D (fieldConjugation f) := by
  change fieldConjugation (Qh h (resolvent D le_rfl (by positivity) (Qh h f))) =
    Qh h (resolvent D le_rfl (by positivity) (Qh h (fieldConjugation f)))
  rw [Qh_conjugation, ← resolvent_conjugation, Qh_conjugation]

theorem Sh_preserves_real {h z : ℝ} (D : Calibration h z) (f : FieldL2)
    (hf : fieldConjugation f = f) : fieldConjugation (Sh D f) = Sh D f := by
  rw [Sh_conjugation, hf]

theorem Sh_supported {h z : ℝ} (D : Calibration h z) (f : FieldL2) (j : Fin 3) :
    ∀ᵐ x ∂(volume : Measure Space), h⁻¹ ≤ ‖x‖ → Sh D f j x = 0 :=
  Qh_supported D.h_pos _ j

#print axioms Sh_conjugation
#print axioms Sh_supported

end Maxwell.Continuum.EffectiveMass
