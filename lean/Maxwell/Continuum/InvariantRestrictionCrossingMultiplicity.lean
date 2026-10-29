import Maxwell.Continuum.InvariantRestrictionCrossing

/-! The finite parameter set is exact for the original unbounded family,
and the full kernel multiplicity budget is bounded by the low dimension. -/

noncomputable section

namespace Maxwell.Continuum.InvariantRestrictionCrossing.Family

open FormPerturbation SelfAdjointResolvent

set_option backward.isDefEq.respectTransparency false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H} {K : Submodule ℂ H} [CompleteSpace K]
variable [FiniteDimensional ℂ K] {W : Set ℝ}
variable (G : Family W A K) (F : InvariantRestriction.Data A K) (hA : IsSelfAdjoint A)

theorem kernel_eq_bot_iff (t : W) :
    (addBounded A (G.perturbation t)).ker = ⊥ ↔ (G.effective F hA t).ker = ⊥ := by
  rw [← Submodule.subsingleton_iff_eq_bot, ← Submodule.subsingleton_iff_eq_bot]
  exact (G.kernelEquiv F hA t).toEquiv.subsingleton_congr

theorem mem_singularParameters (t : W) :
    (t : ℝ) ∈ G.singularParameters F hA ↔
      (addBounded A (G.perturbation t)).ker ≠ ⊥ := by
  change (t : ℝ) ∈ (G.blockFamily F hA).singularParameters ↔ _
  rw [(G.blockFamily F hA).mem_singularParameters]
  exact not_congr (G.kernel_eq_bot_iff F hA t).symm

theorem singularParameters_subset : (↑(G.singularParameters F hA) : Set ℝ) ⊆ W :=
  WindowCrossing.singularParameters_subset W
    (fun t => ((G.blockFamily F hA).effective t).toLinearMap)
    (G.blockFamily F hA).effective_symmetric (G.blockFamily F hA).effective_decrease

include F hA in
/-- All ambient zero-mode multiplicities together fit into the finite low
space. In particular, a repeated eigenvalue spends its full multiplicity. -/
theorem sum_kernel_dimensions_le (s : Finset W) :
    (∑ t ∈ s, Module.finrank ℂ (addBounded A (G.perturbation t)).ker) ≤
      Module.finrank ℂ K := by
  classical
  let T (t : W) : K →ₗ[ℂ] K := (G.effective F hA t).toLinearMap
  have hs : ∀ t ∈ s.image Subtype.val, t ∈ W := by
    intro t ht
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp ht
    exact u.property
  have hm := MonotoneCrossing.sum_kernel_dimensions_le
    (WindowCrossing.extension W T)
    (WindowCrossing.extension_symmetric W T (G.blockFamily F hA).effective_symmetric)
    W (WindowCrossing.extension_decrease W T (G.blockFamily F hA).effective_decrease)
    (s.image Subtype.val) hs
  rw [Finset.sum_image (fun a _ b _ h => Subtype.ext h)] at hm
  calc
    _ = ∑ t ∈ s, Module.finrank ℂ (WindowCrossing.extension W T t).ker := by
      apply Finset.sum_congr rfl
      intro t _
      rw [WindowCrossing.extension_apply W T t]
      exact G.kernel_finrank_eq F hA t
    _ ≤ _ := hm

/-- A concrete bounded inverse, including actual domain membership and both
inverse laws, at every parameter outside the constructed finite set. -/
def inverse (t : W) (ht : (t : ℝ) ∉ G.singularParameters F hA) :
    BoundedInverse (addBounded A (G.perturbation t)) :=
  Classical.choice ((G.inverse_iff_not_mem F hA t).mpr ht)

end Maxwell.Continuum.InvariantRestrictionCrossing.Family
