import Maxwell.Continuum.PECFiniteSpectrum
import Maxwell.Continuum.BoxModesCutoffSpectrum

/-! The finite spectral count for the actual scalar-dielectric PEC box.
The basis, domain, invariant cutoff, both infinite eliminations and the
finite crossing count are all proved dependencies of these statements. -/

noncomputable section

namespace Maxwell.Continuum

set_option backward.isDefEq.respectTransparency false

open SelfAdjointResolvent MeasureTheory

namespace ScalarDielectric

variable (ε : ScalarDielectric) (N : ModeCount.BoxLengths) (hN : ∀ j, 0 < N j)

def boxWindowSpectrum : Finset ℝ :=
  ε.windowSpectrum (BoxModes.boxDomain (fun j => (N j : ℝ)))
    (BoxModes.boxTransverseCutoff N hN)

theorem boxWindowSpectrum_card_le :
    (ε.boxWindowSpectrum N hN).card ≤ ModeCount.spectralCountBudget N :=
  (ε.windowSpectrum_card_le _ _).trans (BoxModes.boxTransverseCutoff_finrank_le N hN)

theorem boxWindowSpectrum_card_le_volume :
    (ε.boxWindowSpectrum N hN).card ≤ 54 * ModeCount.boxVolume N :=
  (ε.boxWindowSpectrum_card_le N hN).trans (ModeCount.spectralCountBudget_le_volume N hN)

theorem boxWindowSpectrum_card_le_physical_volume :
    ((ε.boxWindowSpectrum N hN).card : ℝ) ≤
      54 * (volume (BoxModes.openBox (fun j => (N j : ℝ)))).toReal := by
  exact (Nat.cast_le.mpr (ε.windowSpectrum_card_le _ _)).trans
    (BoxModes.boxTransverseCutoff_finrank_le_physical_volume N hN)

/-- The finite set is exactly the physical real spectrum in the window. -/
theorem boxWindowSpectrum_eq :
    (↑(ε.boxWindowSpectrum N hN) : Set ℝ) =
      realSpectrum (maxwellOperator (BoxModes.boxDomain (fun j => (N j : ℝ))) ε) ∩
        SpectralWindow := by
  ext ell
  constructor
  · intro hell
    have hw := ε.windowSpectrum_subset _ (BoxModes.boxTransverseCutoff N hN) hell
    exact ⟨(ε.mem_windowSpectrum _ (BoxModes.boxTransverseCutoff N hN) ⟨ell, hw⟩).mpr hell, hw⟩
  · rintro ⟨hell, hw⟩
    exact ε.windowSpectrum_covers _ (BoxModes.boxTransverseCutoff N hN) ell hell hw

include hN in
theorem boxWindowSpectrum_finite :
    (realSpectrum (maxwellOperator (BoxModes.boxDomain (fun j => (N j : ℝ))) ε) ∩
      SpectralWindow).Finite := by
  rw [← ε.boxWindowSpectrum_eq N hN]
  exact Finset.finite_toSet _

include hN in
theorem boxWindowKernel_finiteDimensional (t : SpectralWindow) :
    FiniteDimensional ℂ
      (shift (maxwellOperator (BoxModes.boxDomain (fun j => (N j : ℝ))) ε) t).ker :=
  ε.windowKernel_finiteDimensional _ (BoxModes.boxTransverseCutoff N hN) t

include hN in
/-- The full physical eigenvalue multiplicities satisfy the advertised
count; this is stronger than just bounding the number of distinct roots. -/
theorem boxWindowSpectrum_multiplicity_le (s : Finset SpectralWindow) :
    (∑ t ∈ s, Module.finrank ℂ
      (shift (maxwellOperator (BoxModes.boxDomain (fun j => (N j : ℝ))) ε) t).ker) ≤
        ModeCount.spectralCountBudget N :=
  (ε.windowSpectrum_multiplicity_le _ (BoxModes.boxTransverseCutoff N hN) s).trans
    (BoxModes.boxTransverseCutoff_finrank_le N hN)

include hN in
theorem boxWindowSpectrum_multiplicity_le_volume (s : Finset SpectralWindow) :
    (∑ t ∈ s, Module.finrank ℂ
      (shift (maxwellOperator (BoxModes.boxDomain (fun j => (N j : ℝ))) ε) t).ker) ≤
        54 * ModeCount.boxVolume N :=
  (ε.boxWindowSpectrum_multiplicity_le N hN s).trans
    (ModeCount.spectralCountBudget_le_volume N hN)

end ScalarDielectric

end Maxwell.Continuum
