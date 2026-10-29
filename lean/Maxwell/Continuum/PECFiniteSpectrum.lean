import Maxwell.Continuum.InvariantRestrictionCrossingMultiplicity
import Maxwell.Continuum.PECSchurKernel
import Maxwell.Continuum.PECSchurCoercivity
import Maxwell.Continuum.TransverseCutoff

/-! The actual finite-window Maxwell spectrum from a finite free-mode cutoff.
The rectangular-box Fourier construction supplies this cutoff; the spectral
count and resolvent conclusions below are derived from it. -/

noncomputable section

namespace Maxwell.Continuum

set_option backward.isDefEq.respectTransparency false

open TopologicalSpace SelfAdjointResolvent

abbrev SpectralWindow := Set.Icc (-(1 / 4 : ℝ)) (1 / 4)

namespace ScalarDielectric

variable (ε : ScalarDielectric) (Ω : Opens Space) (D : TransverseCutoff Ω)

/-- The actual material Schur family satisfies all high-elimination inputs. -/
def cutoffFamily : InvariantRestrictionCrossing.Family SpectralWindow
    (transverseCurlCurl Ω) D.space where
  perturbation t := ε.transverseSchurPart Ω t t.property.1
  symmetric t := ε.transverseSchurPart_symmetric Ω t t.property.1
  high_coercive t u hu := ε.schurOperator_high_coercive Ω t t.property.1 t.property.2 u
    (D.high u hu)
  decrease a b hab u := ε.schurOperator_strict_antitone Ω a b a.property.1 b.property.1 hab u

def windowSpectrum : Finset ℝ :=
  (ε.cutoffFamily Ω D).singularParameters D.invariant (transverseCurlCurl_selfAdjoint Ω)

theorem windowSpectrum_card_le : (ε.windowSpectrum Ω D).card ≤ Module.finrank ℂ D.space :=
  (ε.cutoffFamily Ω D).singularParameters_card_le D.invariant (transverseCurlCurl_selfAdjoint Ω)

/-- The finite zero set is exactly the real physical Maxwell spectrum in
the window; the assertion concerns genuine bounded inverse failure. -/
theorem mem_windowSpectrum (t : SpectralWindow) :
    (t : ℝ) ∈ realSpectrum (maxwellOperator Ω ε) ↔ (t : ℝ) ∈ ε.windowSpectrum Ω D := by
  have hM := ε.mem_realSpectrum_iff_schur Ω t t.property.1
  have hI := (ε.cutoffFamily Ω D).inverse_iff_not_mem D.invariant
    (transverseCurlCurl_selfAdjoint Ω) t
  change Nonempty (BoundedInverse (ε.schurOperator Ω t t.property.1)) ↔
    (t : ℝ) ∉ ε.windowSpectrum Ω D at hI
  exact hM.trans (by simpa only [not_not] using not_congr hI)

theorem windowSpectrum_covers (ell : ℝ)
    (hell : ell ∈ realSpectrum (maxwellOperator Ω ε)) (hwindow : ell ∈ SpectralWindow) :
    ell ∈ ε.windowSpectrum Ω D := (ε.mem_windowSpectrum Ω D ⟨ell, hwindow⟩).mp hell

theorem windowSpectrum_subset : (↑(ε.windowSpectrum Ω D) : Set ℝ) ⊆ SpectralWindow :=
  (ε.cutoffFamily Ω D).singularParameters_subset D.invariant (transverseCurlCurl_selfAdjoint Ω)

/-- The exact physical nullspace is equivalent to a subspace of the actual
finite cutoff. This is also the finite-multiplicity statement. -/
def windowKernelEquiv (t : SpectralWindow) :
    (shift (maxwellOperator Ω ε) t).ker ≃ₗ[ℂ]
      ((ε.cutoffFamily Ω D).effective D.invariant (transverseCurlCurl_selfAdjoint Ω) t).ker :=
  (ε.schurKernelEquiv Ω t t.property.1).trans
    ((ε.cutoffFamily Ω D).kernelEquiv D.invariant (transverseCurlCurl_selfAdjoint Ω) t)

include D in
theorem windowKernel_finiteDimensional (t : SpectralWindow) :
    FiniteDimensional ℂ (shift (maxwellOperator Ω ε) t).ker :=
  (ε.windowKernelEquiv Ω D t).symm.finiteDimensional

/-- In the counting window every spectral point is an eigenvalue of the
literal unbounded Maxwell operator. -/
theorem mem_windowSpectrum_iff_kernel (t : SpectralWindow) :
    (t : ℝ) ∈ ε.windowSpectrum Ω D ↔ (shift (maxwellOperator Ω ε) t).ker ≠ ⊥ := by
  have h := (ε.cutoffFamily Ω D).mem_singularParameters D.invariant
    (transverseCurlCurl_selfAdjoint Ω) t
  have hk : (shift (maxwellOperator Ω ε) t).ker = ⊥ ↔
      (ε.schurOperator Ω t t.property.1).ker = ⊥ := by
    rw [← Submodule.subsingleton_iff_eq_bot, ← Submodule.subsingleton_iff_eq_bot]
    exact (ε.schurKernelEquiv Ω t t.property.1).toEquiv.subsingleton_congr
  exact h.trans (not_congr hk).symm

/-- Counting with the full geometric multiplicity, for any finite list of
parameters in the window. No kernel is replaced by a single mode. -/
theorem windowSpectrum_multiplicity_le (s : Finset SpectralWindow) :
    (∑ t ∈ s, Module.finrank ℂ (shift (maxwellOperator Ω ε) t).ker) ≤
      Module.finrank ℂ D.space := by
  calc
    _ = ∑ t ∈ s, Module.finrank ℂ (ε.schurOperator Ω t t.property.1).ker := by
      apply Finset.sum_congr rfl
      intro t _
      exact ε.schur_kernel_finrank_eq Ω t t.property.1
    _ ≤ _ := (ε.cutoffFamily Ω D).sum_kernel_dimensions_le D.invariant
      (transverseCurlCurl_selfAdjoint Ω) s

end ScalarDielectric

end Maxwell.Continuum
