import Maxwell.Composition.PhysicalPlatform
import Mathlib.Data.Nat.Size

/-! The emitted fixed-point format is selected from rational amplitude and
readout budgets. Its definition does not inspect the physical output. -/
namespace Maxwell.Composition
open Maxwell.Realization

def selectedFormat (P : PhysicalPlatform) (ε : ℚ) (hε : 0 < ε)
    (n k : ℕ) (amplitude : ℚ) : Target.FixedPointFormat where
  integerBits := (Nat.ceil amplitude).size
  fractionalBits := precisionBits (P.constants.readoutBudget ε (n * k))
    (P.constants.readoutBudget_pos ε (n * k) hε)

theorem selectedFormat_error_bound (P : PhysicalPlatform) (ε : ℚ) (hε : 0 < ε)
    (n k : ℕ) (amplitude : ℚ) :
    2 * P.incrementBound * (n * k : ℕ) /
      (2 : ℚ) ^ (selectedFormat P ε hε n k amplitude).fractionalBits ≤ ε / 4096 := by
  have h := P.constants.readoutUnit_error_bound ε (n * k) hε
  simpa only [selectedFormat, PhysicalConstants.readoutUnit, precisionUnit,
    mul_one_div, show P.constants.incrementBound = P.incrementBound from rfl] using h

theorem selectedFormat_amplitude (P : PhysicalPlatform) (ε : ℚ) (hε : 0 < ε)
    (n k : ℕ) (amplitude : ℚ) :
    amplitude < (2 : ℚ) ^ (selectedFormat P ε hε n k amplitude).integerBits := by
  apply (Nat.le_ceil amplitude).trans_lt
  exact_mod_cast Nat.lt_size_self (Nat.ceil amplitude)

theorem selectedFormat_inRange (P : PhysicalPlatform) (ε : ℚ) (hε : 0 < ε)
    (n k : ℕ) (amplitude : ℚ) (x : ℝ) (hx : |x| ≤ (amplitude : ℝ)) :
    (selectedFormat P ε hε n k amplitude).InRange x := by
  have ha : (amplitude : ℝ) <
      (2 : ℝ) ^ (selectedFormat P ε hε n k amplitude).integerBits := by
    exact_mod_cast selectedFormat_amplitude P ε hε n k amplitude
  obtain ⟨hlo, hhi⟩ := abs_le.mp hx
  exact ⟨by linarith, hhi.trans_lt ha⟩

end Maxwell.Composition
