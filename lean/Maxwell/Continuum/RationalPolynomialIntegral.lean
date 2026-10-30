import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Topology.Algebra.Polynomial

/-! Exact finite integration of rational polynomials at rational endpoints. -/

namespace Maxwell.Continuum.Calibration

open Polynomial MeasureTheory

def polynomialIntegral (p : Polynomial ℚ) (a b : ℚ) : ℚ :=
  ∑ n ∈ Finset.range (p.natDegree+1), p.coeff n*(b^(n+1)-a^(n+1))/(n+1)

theorem polynomialIntegral_eq (p : Polynomial ℚ) (a b : ℚ) :
    (polynomialIntegral p a b : ℝ)=∫ x in (a : ℝ)..(b : ℝ), p.eval₂ (Rat.castHom ℝ) x := by
  simp_rw [Polynomial.eval₂_eq_sum_range]
  rw [intervalIntegral.integral_finsetSum]
  · simp only [polynomialIntegral]
    push_cast
    apply Finset.sum_congr rfl
    intro n _
    rw [intervalIntegral.integral_const_mul, integral_pow]
    change (p.coeff n : ℝ)*((b : ℝ)^(n+1)-(a : ℝ)^(n+1))/((n : ℝ)+1)=
      (p.coeff n : ℝ)*(((b : ℝ)^(n+1)-(a : ℝ)^(n+1))/((n : ℝ)+1))
    ring
  · intro n _
    exact (continuous_const.mul (continuous_id.pow n)).intervalIntegrable _ _

theorem polynomialIntegral_error {p : Polynomial ℚ} {f : ℝ → ℝ} (hf : Continuous f)
    {a b : ℚ} (hab : a≤b) {δ : ℝ}
    (herror : ∀ x ∈ Set.Icc (a : ℝ) (b : ℝ), |f x-p.eval₂ (Rat.castHom ℝ) x|≤δ) :
    |(∫ x in (a : ℝ)..(b : ℝ), f x)-(polynomialIntegral p a b : ℝ)|≤((b-a : ℚ) : ℝ)*δ := by
  rw [polynomialIntegral_eq, ← intervalIntegral.integral_sub (hf.intervalIntegrable _ _)
    ((p.continuous_eval₂ (Rat.castHom ℝ)).intervalIntegrable _ _)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (a : ℝ)) (b := (b : ℝ))
    (f := fun x => f x-p.eval₂ (Rat.castHom ℝ) x) (C := δ) (by
      intro x hx
      rw [Set.uIoc_of_le (by exact_mod_cast hab)] at hx
      simpa only [Real.norm_eq_abs] using herror x ⟨hx.1.le,hx.2⟩)
  rw [Real.norm_eq_abs, abs_of_nonneg (by exact_mod_cast sub_nonneg.mpr hab : (0 : ℝ)≤(b : ℝ)-(a : ℝ))] at h
  simpa only [Rat.cast_sub,mul_comm] using h

#print axioms polynomialIntegral_eq
#print axioms polynomialIntegral_error

end Maxwell.Continuum.Calibration
