import Maxwell.Continuum.BoxModesHigh
import Maxwell.Continuum.TransverseCutoff

/-! The fully proved physical PEC-box cutoff used by material spectral counting. -/

noncomputable section
namespace Maxwell.Continuum.BoxModes

set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped BigOperators

/-- Fully proved physical cutoff data consumed by the actual Maxwell
material-Schur spectral count. -/
def boxTransverseCutoff (N : ModeCount.BoxLengths) (hN : ∀ j, 0 < N j) :
    TransverseCutoff (boxDomain (fun j => (N j : ℝ))) where
  space := lowTransverseSpace N
  finite := lowTransverseSpace_finiteDimensional N hN
  invariant := lowTransverseSpace_invariant N hN
  high := lowTransverseSpace_high N hN

theorem boxTransverseCutoff_finrank_le (N : ModeCount.BoxLengths) (hN : ∀ j, 0 < N j) :
    Module.finrank ℂ (boxTransverseCutoff N hN).space ≤ ModeCount.spectralCountBudget N :=
  lowTransverseSpace_finrank_le N hN

theorem boxTransverseCutoff_finrank_le_volume (N : ModeCount.BoxLengths) (hN : ∀ j, 0 < N j) :
    Module.finrank ℂ (boxTransverseCutoff N hN).space ≤ 54 * ModeCount.boxVolume N :=
  (boxTransverseCutoff_finrank_le N hN).trans (ModeCount.spectralCountBudget_le_volume N hN)

theorem openBox_volume_toReal (N : Fin 3 → ℝ) (hN : ∀ j, 0 ≤ N j) :
    (volume (openBox N)).toReal = ∏ j : Fin 3, N j := by
  have h := integral_openBox_product N hN (fun _ _ => 1)
  simpa [measureReal_def] using h

/-- The dimension estimate in terms of literal Euclidean Lebesgue volume. -/
theorem boxTransverseCutoff_finrank_le_physical_volume
    (N : ModeCount.BoxLengths) (hN : ∀ j, 0 < N j) :
    (Module.finrank ℂ (boxTransverseCutoff N hN).space : ℝ) ≤
      54 * (volume (openBox (fun j => (N j : ℝ)))).toReal := by
  rw [openBox_volume_toReal _ (fun j => by positivity)]
  have h := boxTransverseCutoff_finrank_le_volume N hN
  exact_mod_cast h

#print axioms boxTransverseCutoff
#print axioms boxTransverseCutoff_finrank_le_volume
#print axioms boxTransverseCutoff_finrank_le_physical_volume

end Maxwell.Continuum.BoxModes
