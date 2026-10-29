import Maxwell.Continuum.TranslationContinuity

/-! Physical complex conjugation preserves the actual L² norm. -/

noncomputable section

namespace Maxwell.Continuum

theorem scalarConjugation_norm (f : ScalarL2) : ‖scalarConjugation f‖ = ‖f‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
    scalarConjugation_inner]
  rfl

theorem fieldConjugation_norm (f : FieldL2) : ‖fieldConjugation f‖ = ‖f‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
    fieldConjugation_inner]
  rfl

end Maxwell.Continuum
