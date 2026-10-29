import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Maxwell.Defect.ComplementaryResolvent

/-! Integrating actual regular resolvent differences. The source weights
may vary with momentum; their integrable norm bound keeps the estimate
independent of a choice of eigenbasis. -/

namespace Maxwell.Defect
open MeasureTheory

variable {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {μ : Measure X}

theorem regular_integral_difference_bound
    (R : X → ℝ → F) (weight : X → ℝ) {s t K : ℝ}
    (hs : Integrable (fun x => R x s) μ)
    (ht : Integrable (fun x => R x t) μ)
    (hw : Integrable weight μ)
    (hdiff : ∀ᵐ x ∂μ, ‖R x s - R x t‖ ≤ K * |s - t| * weight x) :
    ‖(∫ x, R x s ∂μ) - ∫ x, R x t ∂μ‖ ≤
      (K * ∫ x, weight x ∂μ) * |s - t| := by
  rw [← integral_sub hs ht]
  have h := norm_integral_le_of_norm_le (hw.const_mul (K * |s - t|)) hdiff
  rw [integral_const_mul] at h
  convert h using 1; ring

theorem regular_integral_difference_bound_const [IsFiniteMeasure μ]
    (R : X → ℝ → F) {s t K : ℝ}
    (hs : Integrable (fun x => R x s) μ)
    (ht : Integrable (fun x => R x t) μ)
    (hdiff : ∀ᵐ x ∂μ, ‖R x s - R x t‖ ≤ K * |s - t|) :
    ‖(∫ x, R x s ∂μ) - ∫ x, R x t ∂μ‖ ≤
      (K * μ.real Set.univ) * |s - t| := by
  rw [← integral_sub hs ht]
  have h := norm_integral_le_of_norm_le_const hdiff
  convert h using 1; ring

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Source compression multiplies a resolvent-difference estimate by the
norm of the concrete bounded compression map. -/
theorem compressed_regular_difference_bound (C : F →L[ℝ] G)
    {R S : F} {K : ℝ} (hRS : ‖R - S‖ ≤ K) :
    ‖C R - C S‖ ≤ ‖C‖ * K := by
  rw [← map_sub]
  exact (C.le_opNorm _).trans (mul_le_mul_of_nonneg_left hRS (norm_nonneg C))

section Resolvent
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
open Maxwell.Spectral.AnalyticEigenbranch

/-- The actual complementary inverse gives the regular integral estimate,
including the selected eigenvalue itself. No difference estimate is a
premise: it follows from the two augmented inverse identities. -/
theorem regularResolvent_integral_difference_bound
    (T P : X → E →L[ℂ] E) (C : X → (E →L[ℂ] E) →L[ℝ] F)
    (weight : X → ℝ) (energy s t g : ℝ) (hg : 0 < g)
    (hs : Integrable (fun x => C x (regularResolvent (T x) (P x) (energy + s))) μ)
    (ht : Integrable (fun x => C x (regularResolvent (T x) (P x) (energy + t))) μ)
    (hw : Integrable weight μ)
    (hdata : ∀ᵐ x ∂μ, P x * P x = P x ∧ P x * T x = T x * P x ∧
      (T x - (energy + s : ℂ) • 1 + P x).IsInvertible ∧
      (T x - (energy + t : ℂ) • 1 + P x).IsInvertible ∧
      ‖regularResolvent (T x) (P x) (energy + s)‖ ≤ g⁻¹ ∧
      ‖regularResolvent (T x) (P x) (energy + t)‖ ≤ g⁻¹ ∧ ‖C x‖ ≤ weight x) :
    ‖(∫ x, C x (regularResolvent (T x) (P x) (energy + s)) ∂μ) -
      ∫ x, C x (regularResolvent (T x) (P x) (energy + t)) ∂μ‖ ≤
      ((∫ x, weight x ∂μ) / g ^ 2) * |s - t| := by
  have hdiff : ∀ᵐ x ∂μ,
      ‖C x (regularResolvent (T x) (P x) (energy + s)) -
        C x (regularResolvent (T x) (P x) (energy + t))‖ ≤
        (g ^ 2)⁻¹ * |s - t| * weight x := by
    filter_upwards [hdata] with x hx
    obtain ⟨hPP, hPT, hsi, hti, hsn, htn, hCn⟩ := hx
    have hd := regularResolvent_difference_norm_le (T x) (P x)
      (energy + s) (energy + t) hPP hPT hsi hti g hg hsn htn
    have heq : ‖(energy + s : ℂ) - (energy + t)‖ = |s - t| := by
      rw [add_sub_add_left_eq_sub, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [heq] at hd
    have hc := compressed_regular_difference_bound (C x) hd
    calc
      _ ≤ ‖C x‖ * (|s - t| / g ^ 2) := hc
      _ ≤ weight x * (|s - t| / g ^ 2) :=
        mul_le_mul_of_nonneg_right hCn (by positivity)
      _ = _ := by ring
  have h := regular_integral_difference_bound
    (fun x a => C x (regularResolvent (T x) (P x) (energy + a))) weight hs ht hw hdiff
  convert h using 1; ring

end Resolvent

end Maxwell.Defect
