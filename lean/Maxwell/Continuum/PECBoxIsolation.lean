import Maxwell.Continuum.PECBoxSpectrum
import Maxwell.Continuum.PECSchurRange
import Maxwell.Continuum.SelfAdjointShiftIsolation

/-! The finite-window Maxwell spectral points are isolated eigenvalues of
finite multiplicity, in the full operator rather than a truncated matrix. -/

noncomputable section

namespace Maxwell.Continuum.ScalarDielectric

set_option backward.isDefEq.respectTransparency false

open SelfAdjointResolvent

variable (ε : ScalarDielectric) (N : ModeCount.BoxLengths) (hN : ∀ j, 0 < N j)

include hN in
theorem box_spectrum_isolated (t : SpectralWindow) :
    ∃ η : ℝ, 0 < η ∧
      ∀ ell ∈ realSpectrum (maxwellOperator (BoxModes.boxDomain (fun j => (N j : ℝ))) ε),
        |ell - (t : ℝ)| < η → ell = (t : ℝ) := by
  let := ε.boxWindowKernel_finiteDimensional N hN t
  exact isolated_of_shift_range_closed _ (maxwellOperator_selfAdjoint _ ε) t
    (ε.window_range_isClosed _ (BoxModes.boxTransverseCutoff N hN) t)

include hN in
/-- Every spectral value in the stated window is a nonzero, finite
dimensional eigenspace and is isolated even at the two window endpoints. -/
theorem box_spectrum_eigenvalue_finite_isolated (t : SpectralWindow)
    (ht : (t : ℝ) ∈ realSpectrum
      (maxwellOperator (BoxModes.boxDomain (fun j => (N j : ℝ))) ε)) :
    (shift (maxwellOperator (BoxModes.boxDomain (fun j => (N j : ℝ))) ε) t).ker ≠ ⊥ ∧
      FiniteDimensional ℂ
        (shift (maxwellOperator (BoxModes.boxDomain (fun j => (N j : ℝ))) ε) t).ker ∧
      ∃ η : ℝ, 0 < η ∧
        ∀ ell ∈ realSpectrum (maxwellOperator (BoxModes.boxDomain (fun j => (N j : ℝ))) ε),
          |ell - (t : ℝ)| < η → ell = (t : ℝ) := by
  refine ⟨?_, ε.boxWindowKernel_finiteDimensional N hN t, ε.box_spectrum_isolated N hN t⟩
  exact (ε.mem_windowSpectrum_iff_kernel _ (BoxModes.boxTransverseCutoff N hN) t).mp
    ((ε.mem_windowSpectrum _ (BoxModes.boxTransverseCutoff N hN) t).mp ht)

end Maxwell.Continuum.ScalarDielectric
