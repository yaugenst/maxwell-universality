import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Local-to-global assembly of a unique minimum

The local and exterior premises below are supplied separately by the
spectral-polynomial and finite certificate developments. The theorem proves
global uniqueness from those regional premises rather than postulating it.
It is not yet a statement that the concrete certificate inputs meet them.
-/

namespace Maxwell.Spectral

/-- Patch closed local neighborhoods and a strict exterior exclusion. The
center ordering may break the symmetry used by an exterior comparator. -/
theorem unique_minimum_of_local_and_exterior
    {X I : Type*} [MetricSpace X]
    (value : X → ℝ) (center : I → X) (energy : I → ℝ)
    (region : I → Set X) (selected : I) (coercivity : ℝ)
    (hc : 0 < coercivity)
    (hselected : value (center selected) = energy selected)
    (horder : ∀ i, i ≠ selected → energy selected < energy i)
    (hlocal : ∀ i x, x ∈ region i →
      energy i + coercivity * dist x (center i) ^ 2 ≤ value x)
    (hcover : ∀ x, (∃ i, x ∈ region i) ∨ energy selected < value x) :
    ∀ x, energy selected ≤ value x ∧
      (value x = energy selected ↔ x = center selected) := by
  intro x
  have henergy : ∀ i, energy selected ≤ energy i := by
    intro i
    by_cases hi : i = selected
    · simpa only [hi] using (le_refl (energy selected))
    · exact le_of_lt (horder i hi)
  have hmin : energy selected ≤ value x := by
    rcases hcover x with ⟨i, hi⟩ | houtside
    · have hquad := hlocal i x hi
      have hnonneg := mul_nonneg (le_of_lt hc) (sq_nonneg (dist x (center i)))
      linarith [henergy i]
    · exact le_of_lt houtside
  refine ⟨hmin, ?_⟩
  constructor
  · intro heq
    rcases hcover x with ⟨i, hi⟩ | houtside
    · have hquad := hlocal i x hi
      have hnonneg := mul_nonneg (le_of_lt hc) (sq_nonneg (dist x (center i)))
      have his : i = selected := by
        by_contra hne
        have hstrict := horder i hne
        linarith
      subst i
      have hz : dist x (center selected) = 0 := by
        have hp : coercivity * dist x (center selected) ^ 2 = 0 := by linarith
        exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hp).resolve_left (ne_of_gt hc))
      exact dist_eq_zero.mp hz
    · linarith
  · intro hx
    simpa only [hx] using hselected

/-- The numerical comparator margin is a real inequality, with no decimal
rounding or spectrum assumption hidden in its arithmetic. -/
theorem global_comparator_margin :
    (23913 : ℝ) / 2500000 + 1 / 500000 <
      157 / 16384 + 1 / 2 ^ 24 - 1023 / 2 ^ 26 := by
  norm_num

theorem material_perturbation_smaller_than_bulk_gap :
    (1023 : ℝ) / 2 ^ 26 < 1 / 4096 := by
  norm_num

theorem concrete_lower_band_separation (Ec : ℝ) (hEc : 239 / 25000 ≤ Ec) :
    (1 / 128 : ℝ) < Ec := by
  linarith

theorem concrete_material_headroom (Ec maximum : ℝ)
    (hEc : Ec ≤ 957 / 100000)
    (hmaximum : maximum ≤ 12 + 1023 / 2 ^ 20) :
    maximum + 64 * Ec < 25 - 12 := by
  linarith

end Maxwell.Spectral
