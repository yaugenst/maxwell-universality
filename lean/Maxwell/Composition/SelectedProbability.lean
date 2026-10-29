import Maxwell.Composition.SelectedSoundness
import Mathlib.Data.Nat.Size

/-! The literal finite-bit detuning draw and the common event for the
constructed finite PEC box. Its count uses the final buffered dimension. -/
noncomputable section
namespace Maxwell.Composition.SelectedInstance.Input
set_option synthInstance.maxSize 1024

variable (I : Input) (R : SelectedPlatform)

def randomBits : ℕ := (16*(I.source.nnz+Fintype.card (I.box R).Edge)^2).size

theorem random_grid : 16*(I.source.nnz+Fintype.card (I.box R).Edge)^2 ≤ 2^I.randomBits R :=
  (Nat.lt_size_self _).le

theorem failure_probability (J : ℕ)
    (hgrid : 16*(I.source.nnz+Fintype.card (I.box R).Edge)^2 ≤ J) :
    ∃ hJ : 0 < J, Probability.gridProbability J hJ (I.bad R J) ≤
      3/(64*(I.source.nnz : ℝ)) :=
  PhysicalBackground.failure_probability R.physical (I.box R) I.source.nnz J
    (PhysicalGram.width R.physical (I.zeta R) (I.zeta_pos R)) I.nnz_pos
    (R.physical.constants.detuningWidth_pos _ (I.zeta_pos R)) hgrid

theorem random_failure_probability :
    Probability.gridProbability (2^I.randomBits R) (pow_pos (by norm_num) _)
      (I.bad R (2^I.randomBits R)) ≤ 3/(64*(I.source.nnz : ℝ)) := by
  obtain ⟨_,h⟩ := I.failure_probability R _ (I.random_grid R)
  exact h

end Maxwell.Composition.SelectedInstance.Input
