import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Rational inverse-polynomial budgets derived from an actual resolvent
norm bound and a checked rational lower enclosure of the spectral edge. -/

namespace Maxwell.Defect

section BanachAlgebra

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
  [CompleteSpace A] [NormOneClass A]

/-- Spectral inversion converts a resolvent norm bound into separation
of the original real spectrum from zero. -/
theorem spectral_gap_of_inverse_norm (H : A) (hH : IsUnit H)
    (C distance : ℝ) (hC : 0 < C) (hdistance : 0 < distance)
    (hinverse : ‖Ring.inverse H‖ ≤ C / distance) :
    ∀ x ∈ spectrum ℝ H, distance / C ≤ |x| := by
  obtain ⟨v, rfl⟩ := hH
  intro x hx
  have hx0 : x ≠ 0 := spectrum.ne_zero_of_mem_of_unit hx
  have hspec : x⁻¹ ∈ spectrum ℝ ((v⁻¹ : Aˣ) : A) := spectrum.inv₀_mem_inv hx
  have hbound : |x|⁻¹ ≤ C / distance := by
    have hh := (spectrum.norm_le_norm_of_mem hspec).trans
      (show ‖((v⁻¹ : Aˣ) : A)‖ ≤ C / distance by simpa only [Ring.inverse_unit] using hinverse)
    simpa only [norm_inv, Real.norm_eq_abs] using hh
  have hh := (div_le_div_iff₀ (abs_pos.mpr hx0) hdistance).mp
    (show 1 / |x| ≤ C / distance by simpa only [one_div] using hbound)
  exact (div_le_iff₀ hC).mpr (by nlinarith)

/-- The executable lower inverse budget uses only rational arithmetic. -/
def rationalInverseGap (M C z lower : ℚ) : ℚ := min M ((lower - z) / C)

/-- A checked lower edge enclosure supplies the finite inverse-polynomial
checker with positive rational norm and spectral-gap budgets. -/
theorem rational_inverse_budget (H : A) (hH : IsUnit H)
    (M C z lower : ℚ) (edge : ℝ)
    (hM : 0 < M) (hC : 0 < C) (hzlower : z < lower) (hlower : (lower : ℝ) ≤ edge)
    (hnorm : ‖H‖ ≤ (M : ℝ))
    (hinverse : ‖Ring.inverse H‖ ≤ (C : ℝ) / (edge - (z : ℝ))) :
    0 < rationalInverseGap M C z lower ∧ rationalInverseGap M C z lower ≤ M ∧
      ‖H‖ ≤ (M : ℝ) ∧
      ∀ x ∈ spectrum ℝ H, (rationalInverseGap M C z lower : ℝ) ≤ |x| := by
  have hC' : (0 : ℝ) < C := by exact_mod_cast hC
  have hzlower' : (z : ℝ) < lower := by exact_mod_cast hzlower
  have hdist : 0 < edge - (z : ℝ) := by linarith
  refine ⟨lt_min hM (div_pos (sub_pos.mpr hzlower) hC), min_le_left _ _, hnorm, ?_⟩
  intro x hx
  have hgap := spectral_gap_of_inverse_norm H hH (C : ℝ) (edge - (z : ℝ)) hC' hdist hinverse x hx
  have hδ : (rationalInverseGap M C z lower : ℝ) ≤ ((lower : ℝ) - z) / C := by
    exact_mod_cast (min_le_right M ((lower - z) / C))
  exact hδ.trans ((div_le_div_of_nonneg_right (sub_le_sub_right hlower _) hC'.le).trans hgap)

end BanachAlgebra

open Filter Topology

/-- A strict real numerator margin admits a fixed rational upper bound
for its constant while preserving the same margin. -/
theorem exists_rational_numerator_constant (K edge : ℝ) (z budget : ℚ)
    (hK : 0 ≤ K) (hz : (z : ℝ) < edge)
    (hmargin : K * Real.sqrt (edge - (z : ℝ)) < (budget : ℝ)) :
    ∃ C : ℚ, 0 < C ∧ K ≤ (C : ℝ) ∧
      (C : ℝ) * Real.sqrt (edge - (z : ℝ)) < (budget : ℝ) := by
  have hsqrt : 0 < Real.sqrt (edge - (z : ℝ)) := Real.sqrt_pos.2 (sub_pos.mpr hz)
  obtain ⟨C, hKC, hC⟩ := exists_rat_btwn ((lt_div_iff₀ hsqrt).2 hmargin)
  exact ⟨C, by exact_mod_cast hK.trans_lt hKC, hKC.le, (lt_div_iff₀ hsqrt).1 hC⟩

/-- Refining rational upper edge brackets eventually verifies the exact
squared rational numerator inequality. No square root is evaluated by
the finite checker. -/
theorem eventually_rational_numerator_budget (C z budget : ℚ) (edge : ℝ)
    (upper : ℕ → ℚ) (hC : 0 ≤ C) (hz : (z : ℝ) < edge) (hbudget : 0 < budget)
    (hmargin : (C : ℝ) * Real.sqrt (edge - (z : ℝ)) < (budget : ℝ))
    (hupper : Tendsto (fun k => (upper k : ℝ)) atTop (𝓝 edge)) :
    ∀ᶠ k in atTop, z < upper k ∧ C ^ 2 * (upper k - z) < budget ^ 2 := by
  have hC' : (0 : ℝ) ≤ C := by exact_mod_cast hC
  have hb' : (0 : ℝ) < budget := by exact_mod_cast hbudget
  have hsq : (C : ℝ) ^ 2 * (edge - (z : ℝ)) < (budget : ℝ) ^ 2 := by
    have hroot := Real.sq_sqrt (sub_nonneg.mpr hz.le)
    have hnonneg := mul_nonneg hC' (Real.sqrt_nonneg (edge - (z : ℝ)))
    nlinarith [sq_nonneg ((budget : ℝ) - (C : ℝ) * Real.sqrt (edge - (z : ℝ)))]
  have hlim : Tendsto (fun k => (C : ℝ) ^ 2 * ((upper k : ℝ) - (z : ℝ)))
      atTop (𝓝 ((C : ℝ) ^ 2 * (edge - (z : ℝ)))) :=
    tendsto_const_nhds.mul (hupper.sub_const _)
  filter_upwards [hupper.eventually_const_lt hz, hlim.eventually_lt_const hsq] with k hk hbound
  exact ⟨by exact_mod_cast hk, by exact_mod_cast hbound⟩

/-- Refining rational lower edge brackets eventually yields strictly
positive executable inverse budgets for every energy below the edge. -/
theorem eventually_rational_inverse_gap (M C z : ℚ) (edge : ℝ)
    (lower : ℕ → ℚ) (hM : 0 < M) (hC : 0 < C) (hz : (z : ℝ) < edge)
    (hlower : Tendsto (fun k => (lower k : ℝ)) atTop (𝓝 edge)) :
    ∀ᶠ k in atTop, z < lower k ∧ 0 < rationalInverseGap M C z (lower k) ∧
      rationalInverseGap M C z (lower k) ≤ M := by
  filter_upwards [hlower.eventually_const_lt hz] with k hk
  have hzl : z < lower k := by exact_mod_cast hk
  exact ⟨hzl, lt_min hM (div_pos (sub_pos.mpr hzl) hC), min_le_left _ _⟩

end Maxwell.Defect
