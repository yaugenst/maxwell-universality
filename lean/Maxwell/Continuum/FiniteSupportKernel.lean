import Maxwell.Continuum.KernelIntegral
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Real.Sqrt

/-! An operator with an actual integral-kernel representative on a set of
finite measure has norm at most the kernel bound times that measure. -/

noncomputable section

namespace Maxwell.Continuum.KernelIntegral

open MeasureTheory
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {s : Set X} (hs : MeasurableSet s) (hμs : μ s ≠ ∞)

include hs hμs

theorem indicator_one_norm :
    ‖indicatorConstLp (E := ℝ) 2 hs hμs 1‖ = Real.sqrt (μ.real s) := by
  rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp only [norm_one, ENNReal.toReal_ofNat, one_mul, Real.sqrt_eq_rpow]

theorem setIntegral_norm_le (f : Lp ℂ 2 μ) :
    ∫ x in s, ‖f x‖ ∂μ ≤ Real.sqrt (μ.real s) * ‖f‖ := by
  let g : Lp ℝ 2 μ := (Lp.memLp f).norm.toLp (fun x => ‖f x‖)
  have hg : g =ᵐ[μ] fun x => ‖f x‖ := MemLp.coeFn_toLp _
  have hgn : ‖g‖ = ‖f‖ := by
    rw [Lp.norm_toLp, eLpNorm_norm _ (Lp.aestronglyMeasurable f), Lp.norm_def]
  have hi := L2.inner_indicatorConstLp_one hs hμs g
  have hid : inner ℝ (indicatorConstLp 2 hs hμs 1) g = ∫ x in s, ‖f x‖ ∂μ := by
    rw [hi]
    exact integral_congr_ae (ae_restrict_of_ae hg)
  rw [← hid]
  calc
    _ ≤ ‖inner ℝ (indicatorConstLp 2 hs hμs 1) g‖ := le_abs_self _
    _ ≤ ‖indicatorConstLp (E := ℝ) 2 hs hμs 1‖ * ‖g‖ := norm_inner_le_norm _ _
    _ = _ := by rw [indicator_one_norm hs hμs, hgn]

theorem norm_le_of_indicator_bound (f : Lp ℂ 2 μ) {C : ℝ}
    (hf : ∀ᵐ x ∂μ, ‖f x‖ ≤ s.indicator (fun _ => C) x) :
    ‖f‖ ≤ C * Real.sqrt (μ.real s) := by
  have hb : ‖f‖ ≤ C * ‖indicatorConstLp (E := ℝ) 2 hs hμs 1‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hf, @indicatorConstLp_coeFn X ℝ _ 2 μ _ s hs hμs 1] with x hx hi
    rw [hi]
    by_cases hxs : x ∈ s
    · simpa [hxs] using hx
    · simpa [hxs] using hx
  simpa only [indicator_one_norm hs hμs] using hb

theorem finite_support_operator_norm
    (T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (K : X → X → ℂ)
    {C : ℝ} (hC : 0 ≤ C) (hK : ∀ x ∈ s, ∀ y ∈ s, ‖K x y‖ ≤ C)
    (hT : ∀ f : Lp ℂ 2 μ,
      T f =ᵐ[μ] s.indicator (fun x => ∫ y in s, K x y * f y ∂μ)) :
    ‖T‖ ≤ C * μ.real s := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC ENNReal.toReal_nonneg)
  intro f
  have hfint : Integrable (fun y => ‖f y‖) (μ.restrict s) :=
    (integrableOn_Lp_of_measure_ne_top f (by norm_num) hμs).norm
  have hrow (x : X) (hx : x ∈ s) :
      ‖∫ y in s, K x y * f y ∂μ‖ ≤ C * Real.sqrt (μ.real s) * ‖f‖ := by
    have hb := norm_integral_le_of_norm_le (f := fun y => K x y * f y) (hfint.const_mul C)
      ((ae_restrict_mem hs).mono fun y hy => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hK x hx y hy) (norm_nonneg _))
    rw [integral_const_mul] at hb
    exact hb.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (setIntegral_norm_le hs hμs f) hC)
  have hbound : ‖T f‖ ≤
      (C * Real.sqrt (μ.real s) * ‖f‖) * Real.sqrt (μ.real s) := by
    apply norm_le_of_indicator_bound hs hμs
    filter_upwards [hT f] with x hx
    rw [hx]
    by_cases hxs : x ∈ s
    · simpa [hxs] using hrow x hxs
    · simp [hxs]
  calc
    _ ≤ _ := hbound
    _ = C * μ.real s * ‖f‖ := by
      calc
        _ = C * ‖f‖ * (Real.sqrt (μ.real s))^2 := by ring
        _ = _ := by
          rw [Real.sq_sqrt (show 0 ≤ μ.real s from ENNReal.toReal_nonneg)]
          ring

end Maxwell.Continuum.KernelIntegral
