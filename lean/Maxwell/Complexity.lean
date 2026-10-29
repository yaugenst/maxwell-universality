import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# The exponent arithmetic in the conditional complexity transfer

This file checks only the arithmetic of the two exponents in
`source_proof/results/logical/kwz_transfer.md`, equation (6.1).
It does not formalize an asymptotic cost model, the physical reduction,
the randomized success argument, or the sparse linear-equation hypothesis.
-/

namespace Maxwell

/-- The larger exponent after retaining both construction and solver costs. -/
noncomputable def composedExponent (θ : ℝ) : ℝ := max (3 / 2) (3 * θ / 2)

/-- Both exponents are strictly below the target exactly under the stated
construction-floor and solver-exponent conditions. -/
theorem composedExponent_lt_iff (θ γ : ℝ) :
    composedExponent θ < γ ↔ (3 : ℝ) / 2 < γ ∧ θ < 2 * γ / 3 := by
  rw [composedExponent, max_lt_iff]
  constructor
  · rintro ⟨hconstruction, hsolver⟩
    exact ⟨hconstruction, by linarith⟩
  · rintro ⟨hconstruction, hsolver⟩
    exact ⟨hconstruction, by linarith⟩

/-- Retaining the construction cost prevents any strict improvement at or
below its exponent, regardless of the solver exponent. -/
theorem composedExponent_not_lt_of_le_floor (θ γ : ℝ)
    (hγ : γ ≤ (3 : ℝ) / 2) : ¬composedExponent θ < γ := by
  intro h
  have hfloor := ((composedExponent_lt_iff θ γ).mp h).1
  linarith

/-- At the boundary solver exponent the composed exponent equals the target;
the strict inequality in the transfer cannot be replaced with equality. -/
theorem composedExponent_at_boundary (γ : ℝ) (hγ : (3 : ℝ) / 2 ≤ γ) :
    composedExponent (2 * γ / 3) = γ := by
  have hsolver : 3 * (2 * γ / 3) / 2 = γ := by linarith
  rw [composedExponent, hsolver, max_eq_right hγ]

end Maxwell
