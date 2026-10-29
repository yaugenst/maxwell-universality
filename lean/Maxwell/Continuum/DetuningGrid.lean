import Mathlib.Probability.Distributions.Uniform
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-!
# Midpoint-grid counting independent of discrete matrix spectra

These generic definitions and proofs are extracted from `Maxwell.Probability`.
Keeping this small dependency surface lets continuum detuning use the finite
uniform law without importing matrix spectral theory or the Yee construction.
-/

namespace Maxwell.Continuum.DetuningGrid

noncomputable section
open Finset
open scoped Classical

/-- The exact midpoint grid, before interpreting its uniform finite law. -/
def midpoint (τ : ℝ) (J j : ℕ) : ℝ := ((j : ℝ) + 1 / 2) * τ / J

/-- A single real spectral value's exceptional grid indices. -/
def nearGrid (τ radius eig : ℝ) (J : ℕ) : Finset ℕ :=
  (Finset.range J).filter (fun j => |eig - midpoint τ J j| < radius)

/-- Counting a finite subset of the integers uses only its extreme points. -/
theorem nat_card_le_span (s : Finset ℕ) (hs : s.Nonempty) :
    s.card ≤ s.max' hs + 1 - s.min' hs := by
  have hsub : s ⊆ Finset.Icc (s.min' hs) (s.max' hs) := by
    intro i hi
    exact Finset.mem_Icc.mpr ⟨s.min'_le i hi, s.le_max' i hi⟩
  simpa only [Nat.card_Icc] using Finset.card_le_card hsub

/-- The interval occupancy estimate, including endpoints conservatively. -/
theorem nearGrid_card_le (τ radius eig : ℝ) (J : ℕ)
    (hτ : 0 < τ) (hradius : 0 ≤ radius) (hJ : 0 < J) :
    ((nearGrid τ radius eig J).card : ℝ) ≤ 2 * radius * J / τ + 1 := by
  let s := nearGrid τ radius eig J
  by_cases hs : s.Nonempty
  · have hmin := (Finset.mem_filter.mp (s.min'_mem hs)).2
    have hmax := (Finset.mem_filter.mp (s.max'_mem hs)).2
    have hext : s.min' hs ≤ s.max' hs := s.min'_le _ (s.max'_mem hs)
    have hc := nat_card_le_span s hs
    have hcR : (s.card : ℝ) ≤ (s.max' hs : ℝ) + 1 - (s.min' hs : ℝ) := by
      have hcR := (Nat.cast_le (α := ℝ)).mpr hc
      rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one] at hcR
      exact hcR
    have hgap : ((s.max' hs : ℝ) - (s.min' hs : ℝ)) * τ / J < 2 * radius := by
      have ha := (abs_lt.mp hmin).2
      have hb := (abs_lt.mp hmax).1
      have heq : ((s.max' hs : ℝ) - (s.min' hs : ℝ)) * τ / J =
          midpoint τ J (s.max' hs) - midpoint τ J (s.min' hs) := by
        dsimp [midpoint]; ring
      rw [heq]
      linarith
    have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
    have hspan : (s.max' hs : ℝ) - (s.min' hs : ℝ) ≤ 2 * radius * J / τ := by
      apply (le_div_iff₀ hτ).mpr
      exact le_of_lt ((div_lt_iff₀ hJR).mp hgap)
    exact hcR.trans (by linarith)
  · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have hnonneg : 0 ≤ 2 * radius * (J : ℝ) / τ := by positivity
    simpa [s, hempty] using (show (0 : ℝ) ≤ 2 * radius * (J : ℝ) / τ + 1 by linarith)


/-- The actual uniform finite distribution, rather than a probability premise. -/
def gridLaw (J : ℕ) (hJ : 0 < J) : PMF ℕ :=
  PMF.uniformOfFinset (Finset.range J) (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hJ))

/-- Exact probability, as a real number, under the finite law. -/
def gridProbability (J : ℕ) (hJ : 0 < J) (event : Finset ℕ) : ℝ :=
  ((gridLaw J hJ).toOuterMeasure (event : Set ℕ)).toReal

theorem gridProbability_eq (J : ℕ) (hJ : 0 < J) (event : Finset ℕ)
    (hevent : event ⊆ Finset.range J) :
    gridProbability J hJ event = (event.card : ℝ) / J := by
  classical
  unfold gridProbability gridLaw
  rw [PMF.toOuterMeasure_uniformOfFinset_apply]
  simp only [Finset.card_range, ENNReal.toReal_div, ENNReal.toReal_natCast]
  congr 2
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_coe, and_iff_right_iff_imp]
  exact fun hj => hevent hj


/-- Every sample lies strictly inside the prescribed detuning interval. -/
theorem midpoint_mem (τ : ℝ) (J j : ℕ) (hτ : 0 < τ) (hj : j < J) :
    0 < midpoint τ J j ∧ midpoint τ J j < τ := by
  have hJ : (0 : ℝ) < J := by exact_mod_cast (Nat.zero_le j).trans_lt hj
  have hjR : (j : ℝ) + 1 ≤ J := by exact_mod_cast hj
  dsimp [midpoint]
  constructor
  · positivity
  · apply (div_lt_iff₀ hJ).mpr
    nlinarith


/-- With dyadic interval width, every emitted midpoint is itself an exact
dyadic with an explicitly bounded denominator exponent. -/
theorem midpoint_dyadic (a : ℤ) (p bits j : ℕ) :
    midpoint ((a : ℝ) / 2^p) (2^bits) j =
      (((2 * (j : ℤ) + 1) * a : ℤ) : ℝ) / 2^(p + bits + 1) := by
  simp only [midpoint, Nat.cast_pow, Nat.cast_ofNat, Int.cast_mul, Int.cast_add,
    Int.cast_ofNat, Int.cast_natCast, pow_add]
  field_simp
  ring

end
end Maxwell.Continuum.DetuningGrid
