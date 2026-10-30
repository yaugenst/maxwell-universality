import Maxwell.Continuum.PoleOscillatoryIntegral
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-! Integration by parts for a conditionally convergent oscillatory
integral, followed by the absolutely convergent derivative identities. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.OscillatoryPole

open Complex Real MeasureTheory Set Filter
open scoped Topology FourierTransform ContDiff

theorem phase_mul_integrable {f : ℝ → ℂ} (hf : Integrable f) (T : ℝ) :
    Integrable (fun u => oscillatoryPhase T u*f u) := by
  apply hf.norm.mono' ((show Continuous (oscillatoryPhase T) from
    continuous_iff_continuousAt.mpr (fun u => (oscillatoryPhase_hasDerivAt T u).continuousAt)).aestronglyMeasurable.mul
      hf.aestronglyMeasurable)
  exact Eventually.of_forall fun u => by
    change ‖oscillatoryPhase T u*f u‖ ≤ ‖f u‖
    rw [norm_mul, oscillatoryPhase_norm, one_mul]

theorem oscillatory_fourier (f : ℝ → ℂ) (T : ℝ) :
    (∫u : ℝ, oscillatoryPhase T u*f u) = 𝓕 f (-T/(2*Real.pi)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  exact Eventually.of_forall fun u => by
    dsimp only
    have hr : -2*Real.pi*u*(-T/(2*Real.pi)) = T*u := by field_simp
    rw [hr, smul_eq_mul]
    rfl

theorem oscillatory_iteratedDeriv {f : ℝ → ℂ} {N : ℕ∞} (hf : ContDiff ℝ N f)
    (hi : ∀n : ℕ, n ≤ N → Integrable (iteratedDeriv n f)) {n : ℕ} (hn : n ≤ N) (T : ℝ) :
    (∫u : ℝ, oscillatoryPhase T u*iteratedDeriv n f u) =
      (-I*(T : ℂ))^n*(∫u : ℝ, oscillatoryPhase T u*f u) := by
  rw [oscillatory_fourier, oscillatory_fourier]
  have he := congrFun (Real.fourier_iteratedDeriv hf hi hn) (-T/(2*Real.pi))
  rw [smul_eq_mul] at he
  convert he using 2
  congr 1
  push_cast
  field_simp

theorem oscillatory_norm_iteratedDeriv {f : ℝ → ℂ} {N : ℕ∞} (hf : ContDiff ℝ N f)
    (hi : ∀n : ℕ, n ≤ N → Integrable (iteratedDeriv n f)) {n : ℕ} (hn : n ≤ N)
    {T : ℝ} (hT : 0 ≤ T) :
    ‖∫u : ℝ, oscillatoryPhase T u*iteratedDeriv n f u‖ =
      T^n*‖∫u : ℝ, oscillatoryPhase T u*f u‖ := by
  rw [oscillatory_iteratedDeriv hf hi hn, norm_mul, norm_pow, norm_mul, norm_neg,
    Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT]

theorem phase_mul_tendsto_zero {f : ℝ → ℂ} {l : Filter ℝ}
    (hf : Tendsto f l (𝓝 0)) (T : ℝ) :
    Tendsto (fun u => oscillatoryPhase T u*f u) l (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa only [norm_mul, oscillatoryPhase_norm, one_mul, norm_zero] using hf.norm

theorem oscillatory_IBP_interval {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {T : ℝ} (hT : 0 < T) (a b : ℝ) :
    (∫u in a..b, oscillatoryPhase T u*f u) =
      (oscillatoryPhase T b*f b-oscillatoryPhase T a*f a-
        ∫u in a..b, oscillatoryPhase T u*deriv f u)/(I*(T : ℂ)) := by
  have hf' : Continuous (deriv f) := by
    simpa only [iteratedDeriv_one] using hf.continuous_iteratedDeriv 1 (by simp)
  have hc : Continuous (oscillatoryPhase T) := continuous_iff_continuousAt.mpr
    (fun u => (oscillatoryPhase_hasDerivAt T u).continuousAt)
  have hi : IntervalIntegrable (fun u => oscillatoryPhase T u*f u) volume a b :=
    (hc.mul hf.continuous).intervalIntegrable a b
  have hi' : IntervalIntegrable (fun u => oscillatoryPhase T u*deriv f u) volume a b :=
    (hc.mul hf').intervalIntegrable a b
  have hd (u : ℝ) : HasDerivAt (fun v => oscillatoryPhase T v*f v)
      ((I*(T : ℂ))*(oscillatoryPhase T u*f u)+oscillatoryPhase T u*deriv f u) u := by
    convert (oscillatoryPhase_hasDerivAt T u).mul ((hf.differentiable (by simp) u).hasDerivAt) using 1
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    ((hi.const_mul (I*(T : ℂ))).add hi')
  rw [intervalIntegral.integral_add (hi.const_mul _) hi', intervalIntegral.integral_const_mul] at he
  apply (eq_div_iff (mul_ne_zero I_ne_zero (by exact_mod_cast hT.ne'))).2
  linear_combination he

theorem oscillatory_first_improper {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hi : Integrable (deriv f)) (htop : Tendsto f atTop (𝓝 0))
    (hbot : Tendsto f atBot (𝓝 0)) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun R : ℝ => ∫u in -R..R, oscillatoryPhase T u*f u) atTop
      (𝓝 (-(∫u : ℝ, oscillatoryPhase T u*deriv f u)/(I*(T : ℂ)))) := by
  have hb : Tendsto (fun R : ℝ => oscillatoryPhase T R*f R-
      oscillatoryPhase T (-R)*f (-R)) atTop (𝓝 (0 : ℂ)) := by
    simpa only [sub_zero, Function.comp_apply] using (phase_mul_tendsto_zero htop T).sub
      ((phase_mul_tendsto_zero hbot T).comp tendsto_neg_atTop_atBot)
  have hd := intervalIntegral_tendsto_integral (phase_mul_integrable hi T)
    tendsto_neg_atTop_atBot tendsto_id
  have hl := (hb.sub hd).div_const (I*(T : ℂ))
  simp only [zero_sub] at hl
  exact hl.congr (fun R => (oscillatory_IBP_interval hf hT (-R) R).symm)

#print axioms oscillatory_first_improper

end Maxwell.Continuum.OscillatoryPole
