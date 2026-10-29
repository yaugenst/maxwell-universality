import Maxwell.Continuum.SelfAdjointIsolation

/-! Translate the punctured spectral gap to an arbitrary real energy. -/

noncomputable section

namespace Maxwell.Continuum.SelfAdjointResolvent

set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem shift_add (A : H →ₗ.[ℂ] H) (σ τ : ℝ) :
    shift (shift A σ) τ = shift A (σ + τ) := by
  refine LinearPMap.ext_iff.mpr ⟨rfl, ?_⟩
  intro x hx hy
  simp only [shift_apply]
  change A ⟨x, hx⟩ - (σ : ℂ) • x - (τ : ℂ) • x =
    A ⟨x, hy⟩ - ((σ + τ : ℝ) : ℂ) • x
  rw [Complex.ofReal_add, add_smul]
  abel

/-- Isolation is in the full real spectrum, including when the point lies
on the boundary of a window used to prove closed range. -/
theorem isolated_of_shift_range_closed (A : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A)
    (σ : ℝ) [CompleteSpace (shift A σ).ker]
    (hclosed : IsClosed ((shift A σ).toFun.range : Set H)) :
    ∃ η : ℝ, 0 < η ∧ ∀ τ ∈ realSpectrum A, |τ - σ| < η → τ = σ := by
  obtain ⟨η, hη, hgap⟩ := exists_punctured_gap (shift A σ) (shift_selfAdjoint A σ hA) hclosed
  refine ⟨η, hη, ?_⟩
  intro τ hτ hnear
  by_contra hne
  have hz : 0 < |τ - σ| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hg := (not_mem_realSpectrum (shift A σ) (τ - σ)).mp (hgap (τ - σ) hz hnear)
  rw [shift_add, show σ + (τ - σ) = τ by ring] at hg
  exact ((not_mem_realSpectrum A τ).mpr hg) hτ

end Maxwell.Continuum.SelfAdjointResolvent
