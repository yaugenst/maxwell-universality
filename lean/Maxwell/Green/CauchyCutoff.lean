import Maxwell.Green.CauchyRemainder
import Maxwell.Green.SmoothRemainder
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Smooth localization of the actual Cauchy regular part. -/

noncomputable section

open Filter Complex Metric Set MeasureTheory
open scoped Topology ContDiff

namespace Maxwell.Green

def cutoffCauchy (χ : ℝ → ℂ) (f : ℂ → ℂ) (center : ℂ) (R : ℝ) (u : ℝ) : ℂ :=
  χ u * cauchyTerm f 0 center R u

theorem contDiff_cutoffCauchy {χ : ℝ → ℂ} {f : ℂ → ℂ} {center : ℂ} {R : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hf : CircleIntegrable f center R)
    (hs : ∀ u ∈ tsupport χ, (u : ℂ) ∉ sphere center |R|) :
    ContDiff ℝ ∞ (cutoffCauchy χ f center R) := by
  apply contDiff_iff_contDiffAt.mpr
  intro u
  by_cases hu : u ∈ tsupport χ
  · have ha := analyticAt_cauchyTerm f 0 hf (hs u hu)
    exact hχ.contDiffAt.mul ((ha.contDiffAt.restrict_scalars ℝ).comp u
      Complex.ofRealCLM.contDiff.contDiffAt)
  · have heq : cutoffCauchy χ f center R =ᶠ[𝓝 u] fun _ => (0 : ℂ) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hu] with x hx
      simp only [cutoffCauchy, hx, Pi.zero_apply, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq heq

theorem cutoffCauchy_hasCompactSupport {χ : ℝ → ℂ} (f : ℂ → ℂ) (center : ℂ) (R : ℝ)
    (hχ : HasCompactSupport χ) : HasCompactSupport (cutoffCauchy χ f center R) :=
  hχ.mul_right

/-- The actual localized analytic regular part has Fourier error `O(T⁻²)`;
its integrability and smoothness follow from the outer-circle representation. -/
theorem cutoffCauchy_fourier_bound {χ : ℝ → ℂ} {f : ℂ → ℂ} {center : ℂ} {R : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hcompact : HasCompactSupport χ)
    (hf : CircleIntegrable f center R)
    (hs : ∀ u ∈ tsupport χ, (u : ℂ) ∉ sphere center |R|)
    {T : ℝ} (hT : 0 < T) :
    ‖∫ u : ℝ, exp (I * (T : ℂ) * u) * cutoffCauchy χ f center R u‖ ≤
      (∫ u : ℝ, ‖deriv (deriv (cutoffCauchy χ f center R)) u‖) / T ^ 2 := by
  have h := contDiff_cutoffCauchy hχ hf hs
  have h' := (contDiff_infty_iff_deriv.mp h).2
  exact compact_support_fourier_bound _ _ _
    (fun u => (contDiff_infty_iff_deriv.mp h).1 u |>.hasDerivAt)
    (fun u => (contDiff_infty_iff_deriv.mp h').1 u |>.hasDerivAt)
    (contDiff_infty_iff_deriv.mp h').2.continuous
    (cutoffCauchy_hasCompactSupport f center R hcompact) hT

theorem deriv_cutoffCauchy {χ : ℝ → ℂ} {f : ℂ → ℂ} {center : ℂ} {R : ℝ}
    (hχ : Differentiable ℝ χ) (hf : CircleIntegrable f center R)
    (hs : ∀ u ∈ tsupport χ, (u : ℂ) ∉ sphere center |R|) (u : ℝ) :
    deriv (cutoffCauchy χ f center R) u =
      deriv χ u * cauchyTerm f 0 center R u + χ u * cauchyTerm f 1 center R u := by
  apply HasDerivAt.deriv
  apply hasDerivAt_cutoff_mul (hχ u)
  intro hu
  simpa only [Nat.zero_add, Nat.cast_one, one_mul] using
    (hasDerivAt_cauchyTerm f 0 hf (hs u hu)).comp_ofReal

/-- The second derivative of the cutoff remainder has an explicit formula
in terms of the first three bounded Cauchy kernels. -/
theorem second_deriv_cutoffCauchy {χ : ℝ → ℂ} {f : ℂ → ℂ} {center : ℂ} {R : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hf : CircleIntegrable f center R)
    (hs : ∀ u ∈ tsupport χ, (u : ℂ) ∉ sphere center |R|) (u : ℝ) :
    deriv (deriv (cutoffCauchy χ f center R)) u =
      deriv (deriv χ) u * cauchyTerm f 0 center R u +
        2 * deriv χ u * cauchyTerm f 1 center R u +
        2 * χ u * cauchyTerm f 2 center R u := by
  have hc := contDiff_infty_iff_deriv.mp hχ
  have hc' := contDiff_infty_iff_deriv.mp hc.2
  have hfirst : deriv (cutoffCauchy χ f center R) = fun v =>
      deriv χ v * cauchyTerm f 0 center R v + χ v * cauchyTerm f 1 center R v :=
    funext (deriv_cutoffCauchy hc.1 hf hs)
  rw [hfirst]
  have hd₀ : HasDerivAt (fun v : ℝ => deriv χ v * cauchyTerm f 0 center R v)
      (deriv (deriv χ) u * cauchyTerm f 0 center R u +
        deriv χ u * cauchyTerm f 1 center R u) u := by
    apply hasDerivAt_cutoff_mul (hc'.1 u)
    intro hu
    simpa only [Nat.zero_add, Nat.cast_one, one_mul] using
      (hasDerivAt_cauchyTerm f 0 hf (hs u (tsupport_deriv_subset hu))).comp_ofReal
  have hd₁ : HasDerivAt (fun v : ℝ => χ v * cauchyTerm f 1 center R v)
      (deriv χ u * cauchyTerm f 1 center R u +
        χ u * (2 * cauchyTerm f 2 center R u)) u := by
    apply hasDerivAt_cutoff_mul (hc.1 u)
    intro hu
    exact (hasDerivAt_cauchyTerm f 1 hf (hs u hu)).comp_ofReal
  convert (hd₀.add hd₁).deriv using 1
  ring

/-- A common bound on the original quotient along the outer circle controls
the second normal derivative uniformly in any transverse parameters. -/
theorem norm_second_deriv_cutoffCauchy_le {χ : ℝ → ℂ} {f : ℂ → ℂ}
    {center : ℂ} {R M K₀ K₁ K₂ : ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hf : CircleIntegrable f center R)
    (hR : 0 < R) (hM : 0 ≤ M) (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hs : ∀ u ∈ tsupport χ, ‖(u : ℂ) - center‖ ≤ R / 2)
    (hb : ∀ z ∈ sphere center R, ‖f z‖ ≤ M)
    (h₀ : ∀ u, ‖χ u‖ ≤ K₀) (h₁ : ∀ u, ‖deriv χ u‖ ≤ K₁)
    (h₂ : ∀ u, ‖deriv (deriv χ) u‖ ≤ K₂) (u : ℝ) :
    ‖deriv (deriv (cutoffCauchy χ f center R)) u‖ ≤
      K₂ * (R * ((2 / R) ^ 1 * M)) +
        2 * K₁ * (R * ((2 / R) ^ 2 * M)) +
        2 * K₀ * (R * ((2 / R) ^ 3 * M)) := by
  have havoid (u : ℝ) (hu : u ∈ tsupport χ) : (u : ℂ) ∉ sphere center |R| := by
    rw [abs_of_pos hR]
    have hball : (u : ℂ) ∈ ball center R := by
      rw [mem_ball, dist_eq_norm]
      exact (hs u hu).trans_lt (by linarith)
    exact ne_of_lt hball
  rw [second_deriv_cutoffCauchy hχ hf havoid]
  by_cases hu : u ∈ tsupport χ
  · have hn₀ := norm_cauchyTerm_le f 0 hR (hs u hu) hb
    have hn₁ := norm_cauchyTerm_le f 1 hR (hs u hu) hb
    have hn₂ := norm_cauchyTerm_le f 2 hR (hs u hu) hb
    calc
      _ ≤ ‖deriv (deriv χ) u‖ * ‖cauchyTerm f 0 center R u‖ +
          2 * ‖deriv χ u‖ * ‖cauchyTerm f 1 center R u‖ +
          2 * ‖χ u‖ * ‖cauchyTerm f 2 center R u‖ := by
        have h := (norm_add_le
          (deriv (deriv χ) u * cauchyTerm f 0 center R u +
            2 * deriv χ u * cauchyTerm f 1 center R u)
          (2 * χ u * cauchyTerm f 2 center R u)).trans
            (add_le_add (norm_add_le _ _) le_rfl)
        simpa only [norm_mul, norm_ofNat] using h
      _ ≤ _ := by gcongr <;> first | exact h₀ u | exact h₁ u | exact h₂ u
  · have hu' : u ∉ tsupport (deriv χ) := fun h => hu (tsupport_deriv_subset h)
    rw [image_eq_zero_of_notMem_tsupport hu, deriv_of_notMem_tsupport hu,
      deriv_of_notMem_tsupport hu']
    simp only [zero_mul, mul_zero, zero_add, norm_zero]
    positivity

/-- A pointwise bound on a fixed compact support is an actual `L¹` bound.
The support measure is independent of every transverse pole parameter. -/
theorem integral_norm_le_support_measure {g : ℝ → ℂ} {s : Set ℝ} {C : ℝ}
    (hs : IsCompact s) (hg : Integrable g) (hzero : ∀ u ∉ s, g u = 0)
    (hC : ∀ u ∈ s, ‖g u‖ ≤ C) :
    (∫ u : ℝ, ‖g u‖) ≤ volume.real s * C := by
  have hi : Integrable (s.indicator (fun _ : ℝ => C)) :=
    (integrable_indicator_iff hs.measurableSet).mpr
      (integrableOn_const (C := C) hs.measure_ne_top)
  calc
    _ ≤ ∫ u : ℝ, s.indicator (fun _ : ℝ => C) u := by
      apply integral_mono_ae hg.norm hi
      apply Eventually.of_forall
      intro u
      by_cases hu : u ∈ s
      · simpa only [Set.indicator_of_mem hu] using hC u hu
      · simp only [hzero u hu, norm_zero, Set.indicator_of_notMem hu, le_refl]
    _ = _ := by rw [integral_indicator_const C hs.measurableSet]; rfl

end Maxwell.Green
