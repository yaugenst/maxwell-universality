import Maxwell.Continuum.AnalyticRealDerivatives
import Maxwell.Continuum.PoleTailJets
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars

/-! Compact oscillatory integrals of a holomorphic amplitude. The
cutoff makes the global real function smooth without requiring a
holomorphic extension outside the actual local chart. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.OscillatoryPole

open Complex Real MeasureTheory Set Filter PeriodicBand Metric
open scoped Topology FourierTransform ContDiff

def cutoffHolomorphic (a : ℝ) (f : ℂ → ℂ) (u : ℝ) : ℂ := complexCutoff a u*f (u : ℂ)

theorem cutoffHolomorphic_zero_near {a : ℝ} (ha : 0 < a) (f : ℂ → ℂ)
    {u : ℝ} (hu : 2*a < |u|) : cutoffHolomorphic a f =ᶠ[𝓝 u] 0 := by
  filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hu] with v hv
  simp only [cutoffHolomorphic, complexCutoff, scaledPsi_eq_zero ha hv.le,
    Complex.ofReal_zero, zero_mul, Pi.zero_apply]

theorem cutoffHolomorphic_contDiff {a R : ℝ} (ha : 0 < a) (hR : 2*a < R)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) :
    ContDiff ℝ (⊤ : ℕ∞) (cutoffHolomorphic a f) := by
  rw [contDiff_iff_contDiffAt]
  intro u
  by_cases hu : |u| < R
  · have haF := hf (u : ℂ) (by simpa only [mem_closedBall, dist_zero_right,
        Complex.norm_real, Real.norm_eq_abs] using hu.le)
    have hc : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => f (x : ℂ)) u :=
      ((haF.contDiffAt : ContDiffAt ℂ (⊤ : ℕ∞) f (u : ℂ)).restrict_scalars ℝ).comp u
        Complex.ofRealCLM.contDiff.contDiffAt
    exact (complexCutoff_contDiff a).contDiffAt.mul hc
  · have hz := cutoffHolomorphic_zero_near ha f (lt_of_lt_of_le hR (le_of_not_gt hu))
    exact contDiffAt_const.congr_of_eventuallyEq hz

theorem cutoffHolomorphic_jet_zero {a : ℝ} (ha : 0 < a) (f : ℂ → ℂ)
    {u : ℝ} (hu : 2*a < |u|) (n : ℕ) : iteratedDeriv n (cutoffHolomorphic a f) u = 0 := by
  rw [(cutoffHolomorphic_zero_near ha f hu).iteratedDeriv_eq n]
  simp

theorem cutoffHolomorphic_jet_compact {a : ℝ} (ha : 0 < a) (f : ℂ → ℂ) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n (cutoffHolomorphic a f)) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Icc (-2*a) (2*a)))
  intro u hu
  have hb : |u| ≤ 2*a := by
    by_contra hb
    exact hu (cutoffHolomorphic_jet_zero ha f (lt_of_not_ge hb) n)
  exact ⟨by linarith only [(abs_le.mp hb).1], (abs_le.mp hb).2⟩

theorem cutoffHolomorphic_jets {a R : ℝ} (hR : 2*a ≤ R)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    {u : ℝ} (hu : |u| ≤ 2*a) (n : ℕ) :
    iteratedDeriv n (cutoffHolomorphic a f) u =
      ∑ k ∈ Finset.range (n+1), (n.choose k : ℂ)*
        ((iteratedDeriv k (scaledPsi a) u : ℝ) : ℂ)*iteratedDeriv (n-k) f (u : ℂ) := by
  have haF := hf (u : ℂ) (by simpa only [mem_closedBall, dist_zero_right,
    Complex.norm_real, Real.norm_eq_abs] using hu.trans hR)
  have hc : ContDiffAt ℝ (n : ℕ∞ω) (fun x : ℝ => f (x : ℂ)) u :=
    ((haF.contDiffAt : ContDiffAt ℂ (n : ℕ∞ω) f (u : ℂ)).restrict_scalars ℝ).comp u
      Complex.ofRealCLM.contDiff.contDiffAt
  unfold cutoffHolomorphic
  rw [iteratedDeriv_fun_mul ((complexCutoff_contDiff a).contDiffAt.of_le (by simp)) hc]
  simp only [complexCutoff_iteratedDeriv, analyticAt_iteratedDeriv_ofReal haF]

theorem cutoffHolomorphic_jet_integrable {a R : ℝ} (ha : 0 < a) (hR : 2*a < R)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (n : ℕ) :
    Integrable (iteratedDeriv n (cutoffHolomorphic a f)) :=
  ((cutoffHolomorphic_contDiff ha hR hf).continuous_iteratedDeriv n (by simp)).integrable_of_hasCompactSupport
    (cutoffHolomorphic_jet_compact ha f n)

theorem cutoffHolomorphic_jet_l1 {a R : ℝ} (ha : 0 < a) (hR : 2*a < R)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (n : ℕ)
    {C : ℝ} (_hC : 0 ≤ C) (hb : ∀u : ℝ, |u| ≤ 2*a → ‖iteratedDeriv n (cutoffHolomorphic a f) u‖ ≤ C) :
    (∫u : ℝ, ‖iteratedDeriv n (cutoffHolomorphic a f) u‖) ≤ 4*a*C := by
  have he : (fun u : ℝ => ‖iteratedDeriv n (cutoffHolomorphic a f) u‖) =
      (Icc (-2*a) (2*a)).indicator (fun u => ‖iteratedDeriv n (cutoffHolomorphic a f) u‖) := by
    funext u
    by_cases hu : u ∈ Icc (-2*a) (2*a)
    · rw [indicator_of_mem hu]
    · rw [indicator_of_notMem hu, cutoffHolomorphic_jet_zero ha f, norm_zero]
      exact lt_of_not_ge (fun hx => hu ⟨by linarith only [(abs_le.mp hx).1], (abs_le.mp hx).2⟩)
  rw [he, integral_indicator measurableSet_Icc]
  calc
    _ ≤ ∫_u in Icc (-2*a) (2*a), C := setIntegral_mono_on
      ((cutoffHolomorphic_jet_integrable ha hR hf n).norm.integrableOn)
      (integrableOn_const (by simp : volume (Icc (-2*a) (2*a)) ≠ ⊤)) measurableSet_Icc
      (fun u hu => hb u (abs_le.mpr ⟨by linarith only [hu.1], hu.2⟩))
    _ = _ := by
      simp only [setIntegral_const, Measure.real, Real.volume_Icc, smul_eq_mul]
      rw [ENNReal.toReal_ofReal (by linarith only [ha] : 0 ≤ 2*a-(-2*a))]
      ring

theorem cutoffHolomorphic_oscillatory_bound {a R : ℝ} (ha : 0 < a) (hR : 2*a < R)
    {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (n : ℕ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀u : ℝ, |u| ≤ 2*a → ‖iteratedDeriv n (cutoffHolomorphic a f) u‖ ≤ C)
    {T : ℝ} (hT : 0 < T) :
    ‖∫u : ℝ, oscillatoryPhase T u*cutoffHolomorphic a f u‖ ≤ 4*a*C/T^n := by
  have he := oscillatory_norm_iteratedDeriv (cutoffHolomorphic_contDiff ha hR hf)
    (fun k _ => cutoffHolomorphic_jet_integrable ha hR hf k) (n := n) (by simp) hT.le
  apply (le_div_iff₀ (pow_pos hT n)).mpr
  rw [mul_comm, ← he]
  calc
    _ ≤ ∫u : ℝ, ‖oscillatoryPhase T u*iteratedDeriv n (cutoffHolomorphic a f) u‖ := norm_integral_le_integral_norm _
    _ = ∫u : ℝ, ‖iteratedDeriv n (cutoffHolomorphic a f) u‖ := by
      simp only [norm_mul, oscillatoryPhase_norm, one_mul]
    _ ≤ _ := cutoffHolomorphic_jet_l1 ha hR hf n hC hb

#print axioms cutoffHolomorphic_oscillatory_bound

end Maxwell.Continuum.OscillatoryPole
