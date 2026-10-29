import Maxwell.Continuum.FiniteSupportKernel
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! The finite-support kernel bound in weak form. An exact identity for
all L² pairings suffices; no pointwise representative of the output is
needed to derive the operator-norm estimate. -/

noncomputable section

namespace Maxwell.Continuum.KernelIntegral

open MeasureTheory
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {s : Set X} (hs : MeasurableSet s) (hμs : μ s ≠ ∞)

include hs hμs

theorem finite_support_operator_norm_of_pairing
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (K : X → X → ℂ)
    {C : ℝ} (hC : 0 ≤ C) (hK : ∀ x ∈ s, ∀ y ∈ s, ‖K x y‖ ≤ C)
    (hT : ∀ f g : Lp ℂ 2 μ, inner ℂ g (T f) =
      ∫ x in s, star (g x) * (∫ y in s, K x y * f y ∂μ) ∂μ) :
    ‖T‖ ≤ C * μ.real s := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le (mul_nonneg hC ENNReal.toReal_nonneg)
  intro f g hf hg
  have hfint : Integrable (fun y => ‖f y‖) (μ.restrict s) :=
    (integrableOn_Lp_of_measure_ne_top f (by norm_num) hμs).norm
  have hgint : Integrable (fun x => ‖g x‖) (μ.restrict s) :=
    (integrableOn_Lp_of_measure_ne_top g (by norm_num) hμs).norm
  have hrow (x : X) (hx : x ∈ s) :
      ‖∫ y in s, K x y * f y ∂μ‖ ≤ C * Real.sqrt (μ.real s) := by
    have hb := norm_integral_le_of_norm_le (f := fun y => K x y * f y) (hfint.const_mul C)
      ((ae_restrict_mem hs).mono fun y hy => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hK x hx y hy) (norm_nonneg _))
    rw [integral_const_mul] at hb
    have hh := setIntegral_norm_le hs hμs f
    rw [hf, mul_one] at hh
    exact hb.trans (mul_le_mul_of_nonneg_left hh hC)
  have hpair : ‖inner ℂ g (T f)‖ ≤ C * μ.real s := by
    rw [hT f g]
    have hb := norm_integral_le_of_norm_le
      (f := fun x => star (g x) * (∫ y in s, K x y * f y ∂μ))
      (hgint.const_mul (C * Real.sqrt (μ.real s)))
      ((ae_restrict_mem hs).mono fun x hx => by
        rw [norm_mul, norm_star]
        simpa only [mul_comm (C * Real.sqrt (μ.real s))] using
          mul_le_mul_of_nonneg_left (hrow x hx) (norm_nonneg (g x)))
    rw [integral_const_mul] at hb
    have hh := setIntegral_norm_le hs hμs g
    rw [hg, mul_one] at hh
    calc
      _ ≤ (C * Real.sqrt (μ.real s)) * ∫ x in s, ‖g x‖ ∂μ := hb
      _ ≤ (C * Real.sqrt (μ.real s)) * Real.sqrt (μ.real s) :=
        mul_le_mul_of_nonneg_left hh (mul_nonneg hC (Real.sqrt_nonneg _))
      _ = C * μ.real s := by
        rw [mul_assoc, ← pow_two, Real.sq_sqrt (show 0 ≤ μ.real s from ENNReal.toReal_nonneg)]
  have hre : RCLike.re (inner ℂ (T f) g) = RCLike.re (inner ℂ g (T f)) :=
    inner_re_symm _ _
  rw [hre]
  exact (RCLike.re_le_norm _).trans hpair

end Maxwell.Continuum.KernelIntegral
