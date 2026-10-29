import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic

/-! # Local Taylor estimates used by the pole and saddle calculation -/

open Filter Metric Asymptotics
open scoped Topology

namespace Maxwell.Green

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- Analyticity supplies an actual uniform local linear amplitude bound. -/
theorem analytic_amplitude_bound {a : W → ℂ} (ha : AnalyticAt ℂ a 0) :
    ∃ K > 0, ∃ δ > 0, ∀ w, ‖w‖ < δ → ‖a w - a 0‖ ≤ K * ‖w‖ := by
  obtain ⟨s, hs⟩ := ha
  obtain ⟨K, hK, hbound⟩ := isBigO_iff'.mp (hs.isBigO_sub_partialSum_pow 1)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hbound
  refine ⟨K, hK, δ, hδ, fun w hw => ?_⟩
  have h := hball (by simpa only [dist_zero_right] using hw)
  simpa [FormalMultilinearSeries.partialSum, hs.coeff_zero] using h

/-- At a stationary analytic root, the second homogeneous power-series term
approximates the phase with a uniform cubic error on a definite neighborhood. -/
theorem analytic_quadratic_remainder {p : W → ℂ} {s : FormalMultilinearSeries ℂ W ℂ}
    (hs : HasFPowerSeriesAt p s 0) (hp₀ : p 0 = 0) (hp₁ : fderiv ℂ p 0 = 0) :
    ∃ K > 0, ∃ δ > 0, ∀ w, ‖w‖ < δ →
      ‖p w - s 2 (fun _ => w)‖ ≤ K * ‖w‖ ^ 3 := by
  have hlinear (w : W) : s 1 (fun _ => w) = 0 := by
    have h := congrArg (fun L : W →L[ℂ] ℂ => L w) hp₁
    rw [hs.fderiv_eq] at h
    have hfin : Fin.snoc (0 : Fin 0 → W) w = fun _ : Fin 1 => w := by
      ext i
      fin_cases i
      rfl
    simpa only [continuousMultilinearCurryFin1_apply, zero_apply, hfin] using h
  have hpartial (w : W) : s.partialSum 3 w = s 2 (fun _ => w) := by
    simp [FormalMultilinearSeries.partialSum, Finset.sum_range_succ,
      hs.coeff_zero, hp₀, hlinear]
  obtain ⟨K, hK, hbound⟩ := isBigO_iff'.mp (hs.isBigO_sub_partialSum_pow 3)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hbound
  refine ⟨K, hK, δ, hδ, fun w hw => ?_⟩
  have h := hball (by simpa only [dist_zero_right] using hw)
  simpa [hpartial, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (norm_nonneg w) 3)] using h

/-- A positive imaginary quadratic form remains positive after a sufficiently
small cubic perturbation. -/
theorem imaginary_quadratic_lower_bound {p q : ℂ} {c K ρ : ℝ}
    (hq : c * ρ ^ 2 ≤ q.im)
    (herr : ‖p - q‖ ≤ K * ρ ^ 3) (hsmall : K * ρ ≤ c / 2) :
    c / 2 * ρ ^ 2 ≤ p.im := by
  have him : q.im - p.im ≤ ‖p - q‖ := by
    simpa only [Complex.sub_im, norm_sub_rev] using Complex.im_le_norm (q - p)
  have herror : K * ρ ^ 3 ≤ c / 2 * ρ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hsmall (sq_nonneg ρ)]
  linarith

omit [NormedSpace ℂ W] in
/-- An explicit radius converts the local cubic remainder into a positive
imaginary Gaussian damping estimate. -/
theorem cubic_perturbation_has_positive_imaginary_part
    {p q : W → ℂ} {K δ c : ℝ} (hK : 0 < K) (hδ : 0 < δ) (hc : 0 < c)
    (herr : ∀ w, ‖w‖ < δ → ‖p w - q w‖ ≤ K * ‖w‖ ^ 3)
    (hq : ∀ w, c * ‖w‖ ^ 2 ≤ (q w).im) :
    ∃ r > 0, ∀ w, ‖w‖ < r → c / 2 * ‖w‖ ^ 2 ≤ (p w).im := by
  refine ⟨min δ (c / (2 * K)), lt_min hδ (by positivity), ?_⟩
  intro w hw
  have hwδ : ‖w‖ < δ := lt_of_lt_of_le hw (min_le_left _ _)
  have hwc : ‖w‖ < c / (2 * K) := lt_of_lt_of_le hw (min_le_right _ _)
  apply imaginary_quadratic_lower_bound (hq w) (herr w hwδ)
  have h := (lt_div_iff₀ (by positivity : 0 < 2 * K)).mp hwc
  nlinarith

/-- Real transverse coordinates as a point in the complexified analytic
parameter space. -/
def realTransverse (w : ℂ) : ℂ × ℂ := ((w.re : ℂ), (w.im : ℂ))

theorem norm_realTransverse_le (w : ℂ) : ‖realTransverse w‖ ≤ ‖w‖ := by
  rw [realTransverse, Prod.norm_def, max_le_iff]
  exact ⟨by simpa using Complex.abs_re_le_norm w,
    by simpa using Complex.abs_im_le_norm w⟩

/-- Restricting the complex analytic chart to its real transverse plane keeps
the cubic bound in the Euclidean transverse radius. -/
theorem restrict_cubic_bound {p q : ℂ × ℂ → ℂ} {K δ : ℝ} (hK : 0 ≤ K)
    (h : ∀ v, ‖v‖ < δ → ‖p v - q v‖ ≤ K * ‖v‖ ^ 3) :
    ∀ w : ℂ, ‖w‖ < δ →
      ‖p (realTransverse w) - q (realTransverse w)‖ ≤ K * ‖w‖ ^ 3 := by
  intro w hw
  exact (h _ ((norm_realTransverse_le w).trans_lt hw)).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_realTransverse_le w) 3) hK)

end Maxwell.Green
