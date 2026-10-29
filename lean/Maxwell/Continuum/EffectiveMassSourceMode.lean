import Maxwell.Continuum.EffectiveMassModeH1

/-! The compactly supported source of an actual auxiliary eigenmode.
Its exact equation uses Qh²=Wh and the constructed physical R0; it does
not assert an isolated eigenstate of the uncut infinite Maxwell operator. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory Auxiliary EigenTranslation

attribute [local irreducible] Auxiliary.resolvent

def sourceMode (h : ℝ) (u : FieldL2) : FieldL2 := Qh h u

theorem sourceMode_ae (h : ℝ) (u : FieldL2) (j : Fin 3) :
    sourceMode h u j =ᵐ[volume] fun x => (Well.qw (h • x) : ℂ) * u j x := Qh_ae h u j

theorem sourceMode_supported {h : ℝ} (hh : 0 < h) (u : FieldL2) (j : Fin 3) :
    ∀ᵐ x ∂(volume : Measure Space), h⁻¹ ≤ ‖x‖ → sourceMode h u j x = 0 :=
  Qh_supported hh u j

theorem sourceMode_real (h : ℝ) {u : FieldL2} (hu : fieldConjugation u = u) :
    fieldConjugation (sourceMode h u) = sourceMode h u := by
  change fieldConjugation (Qh h u) = Qh h u
  rw [Qh_conjugation, hu]

theorem sourceMode_norm_le (h : ℝ) (u : FieldL2) : ‖sourceMode h u‖ ≤ ‖u‖ := by
  simpa only [sourceMode, one_mul] using (Qh h).le_of_opNorm_le (Qh_norm_le h) u

theorem Sh_eigenvector_supported {h z μ : ℝ} (D : Calibration h z) {u : FieldL2}
    (hμ : μ ≠ 0) (hu : Sh D u = (μ : ℂ) • u) (j : Fin 3) :
    ∀ᵐ x ∂(volume : Measure Space), h⁻¹ ≤ ‖x‖ → u j x = 0 := by
  have hj : Sh D u j = (μ : ℂ) • u j := congrArg (fun v : FieldL2 => v j) hu
  filter_upwards [Sh_supported D u j, Lp.coeFn_smul (μ : ℂ) (u j)] with x hs hm hx
  have he : ((μ : ℂ) • u j : ScalarL2) x = 0 := by rw [← hj]; exact hs hx
  rw [hm] at he
  change (μ : ℂ) * u j x = 0 at he
  exact (mul_eq_zero.mp he).resolve_left (Complex.ofReal_ne_zero.mpr hμ)

theorem sourceMode_ne_zero {h z μ : ℝ} (D : Calibration h z) {u : FieldL2}
    (hμ : μ ≠ 0) (hu : Sh D u = (μ : ℂ) • u) (hu0 : u ≠ 0) : sourceMode h u ≠ 0 := by
  intro hz
  have hs : Sh D u = 0 := by
    change Qh h (resolvent D le_rfl (by positivity) (sourceMode h u)) = 0
    rw [hz, map_zero, map_zero]
  have he : (μ : ℂ) • u = 0 := hu.symm.trans hs
  exact hu0 ((smul_eq_zero.mp he).resolve_left (Complex.ofReal_ne_zero.mpr hμ))

theorem sourceMode_equation {h z μ : ℝ} (D : Calibration h z) {u : FieldL2}
    (hμ : μ ≠ 0) (hu : Sh D u = (μ : ℂ) • u) :
    sourceMode h u = (μ : ℂ)⁻¹ • Wh h (resolvent D le_rfl (by positivity) (sourceMode h u)) := by
  have he : Wh h (resolvent D le_rfl (by positivity) (sourceMode h u)) =
      (μ : ℂ) • sourceMode h u := by
    calc
      _ = Qh h (Sh D u) := by rw [← Qh_square]; rfl
      _ = (μ : ℂ) • sourceMode h u := by rw [hu, map_smul]; rfl
  rw [he, smul_smul, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hμ), one_smul]

theorem isolatedMode_zeroExtension_H1 {h z μ : ℝ} {u : FieldL2}
    (D : Calibration h z) (hu : IsolatedRealMode (Sh D) μ (modeGap h) u) (hμ : μ ≠ 0) :
    (∀ j : Fin 3, ∀ᵐ x ∂(volume : Measure Space), h⁻¹ ≤ ‖x‖ → u j x = 0) ∧
      (Sh_modeH1 D hu).norm ≤ (2 : ℝ)^512 * (h^2)⁻¹ :=
  ⟨fun j => Sh_eigenvector_supported D hμ hu.eigenvector j, Sh_modeH1_norm_le D hu⟩

#print axioms sourceMode_equation
#print axioms isolatedMode_zeroExtension_H1

end Maxwell.Continuum.EffectiveMass
