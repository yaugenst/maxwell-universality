import Maxwell.Green.FourierPole
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Localizing the real Fourier pole by two integrations by parts.
Derivative and integrability premises below concern the ordinary complement
amplitude, rather than an assumed Fourier-error estimate. -/

namespace Maxwell.Green

open MeasureTheory Filter Set Complex
open scoped Topology ContDiff

theorem norm_oscillatory_exp (T u : ℝ) : ‖Complex.exp (I * (T : ℂ) * u)‖ = 1 := by
  simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem integrable_oscillatory_mul (T : ℝ) {g : ℝ → ℂ} (hg : Integrable g) :
    Integrable (fun u : ℝ => Complex.exp (I * (T : ℂ) * u) * g u) := by
  apply hg.bdd_mul (c := 1) (Continuous.aestronglyMeasurable (by fun_prop))
  exact Filter.Eventually.of_forall (fun u => (norm_oscillatory_exp T u).le)

theorem tendsto_oscillatory_mul_zero (T : ℝ) {g : ℝ → ℂ} {l : Filter ℝ}
    (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun u : ℝ => Complex.exp (I * (T : ℂ) * u) * g u) l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [norm_mul, norm_oscillatory_exp, one_mul, norm_zero] using hg.norm

/-- Exact finite-interval integration by parts for the oscillatory amplitude. -/
theorem oscillatory_ibp_interval (g g₁ : ℝ → ℂ)
    (hd : ∀ u, HasDerivAt g (g₁ u) u) (hg₁ : Integrable g₁)
    {T : ℝ} (hT : T ≠ 0) (a b : ℝ) :
    (∫ u in a..b, Complex.exp (I * (T : ℂ) * u) * g u) =
      (I * (T : ℂ))⁻¹ *
        (Complex.exp (I * (T : ℂ) * b) * g b -
         Complex.exp (I * (T : ℂ) * a) * g a -
         ∫ u in a..b, Complex.exp (I * (T : ℂ) * u) * g₁ u) := by
  have hc : Continuous g := continuous_iff_continuousAt.mpr (fun u => (hd u).continuousAt)
  have hcg : Continuous (fun u : ℝ => Complex.exp (I * (T : ℂ) * u) * g u) := by fun_prop
  have hi₁ := (integrable_oscillatory_mul T hg₁).intervalIntegrable (a := a) (b := b)
  have hder : ∀ u : ℝ, HasDerivAt (fun v : ℝ => Complex.exp (I * (T : ℂ) * v) * g v)
      (I * (T : ℂ) * (Complex.exp (I * (T : ℂ) * u) * g u) +
        Complex.exp (I * (T : ℂ) * u) * g₁ u) u := by
    intro u
    have he := (((hasDerivAt_id (u : ℂ)).const_mul (I * (T : ℂ))).cexp).comp_ofReal
    convert he.mul (hd u) using 1
    · rfl
    · dsimp
      ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hder u)
    (((hcg.const_mul (I * (T : ℂ))).intervalIntegrable a b).add hi₁)
  rw [intervalIntegral.integral_add
      ((hcg.const_mul (I * (T : ℂ))).intervalIntegrable a b) hi₁,
    intervalIntegral.integral_const_mul] at h
  have hiT : I * (T : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hT)
  apply mul_left_cancel₀ hiT
  rw [← mul_assoc, mul_inv_cancel₀ hiT, one_mul]
  exact eq_sub_of_add_eq h

/-- One integration by parts gives the improper Fourier transform from an
integrable ordinary derivative and vanishing endpoint amplitude. -/
theorem tendsto_oscillatory_integral_of_derivative (g g₁ : ℝ → ℂ)
    (hd : ∀ u, HasDerivAt g (g₁ u) u) (hg₁ : Integrable g₁)
    (hg : Tendsto g (Bornology.cobounded ℝ) (𝓝 0)) {T : ℝ} (hT : T ≠ 0) :
    Tendsto (fun R : ℝ => ∫ u in -R..R, Complex.exp (I * (T : ℂ) * u) * g u)
      atTop (𝓝 (-(I * (T : ℂ))⁻¹ * ∫ u : ℝ, Complex.exp (I * (T : ℂ) * u) * g₁ u)) := by
  have hp := (tendsto_oscillatory_mul_zero T hg).mono_left IsOrderBornology.atTop_le_cobounded
  have hn := ((tendsto_oscillatory_mul_zero T hg).mono_left
    IsOrderBornology.atBot_le_cobounded).comp tendsto_neg_atTop_atBot
  have hi := intervalIntegral_tendsto_integral (integrable_oscillatory_mul T hg₁)
    tendsto_neg_atTop_atBot tendsto_id
  have h := ((hp.sub hn).sub hi).const_mul (I * (T : ℂ))⁻¹
  have h' := h.congr (fun R => (oscillatory_ibp_interval g g₁ hd hg₁ hT (-R) R).symm)
  simpa only [sub_self, zero_sub, mul_neg, neg_mul] using h'

/-- Two integrations by parts give an exact second-derivative representation
of the improper oscillatory tail. -/
theorem tendsto_oscillatory_integral_second_derivative (g g₁ g₂ : ℝ → ℂ)
    (hd : ∀ u, HasDerivAt g (g₁ u) u) (hd₁ : ∀ u, HasDerivAt g₁ (g₂ u) u)
    (hg₁ : Integrable g₁) (hg₂ : Integrable g₂)
    (hg : Tendsto g (Bornology.cobounded ℝ) (𝓝 0))
    (hg' : Tendsto g₁ (Bornology.cobounded ℝ) (𝓝 0)) {T : ℝ} (hT : T ≠ 0) :
    Tendsto (fun R : ℝ => ∫ u in -R..R, Complex.exp (I * (T : ℂ) * u) * g u)
      atTop (𝓝 ((I * (T : ℂ))⁻¹ ^ 2 *
        ∫ u : ℝ, Complex.exp (I * (T : ℂ) * u) * g₂ u)) := by
  have h₁ := tendsto_oscillatory_integral_of_derivative g₁ g₂ hd₁ hg₂ hg' hT
  have h₂ := intervalIntegral_tendsto_integral (integrable_oscillatory_mul T hg₁)
    tendsto_neg_atTop_atBot tendsto_id
  have heq := tendsto_nhds_unique h₂ h₁
  have h := tendsto_oscillatory_integral_of_derivative g g₁ hd hg₁ hg hT
  rw [heq] at h
  have halg (z w : ℂ) : -z * (-z * w) = z ^ 2 * w := by ring
  simpa only [halg] using h

/-- The exact second-derivative remainder has the uniform `T⁻²` estimate. -/
theorem norm_second_derivative_remainder (g₂ : ℝ → ℂ) {T : ℝ} (hT : 0 < T) :
    ‖(I * (T : ℂ))⁻¹ ^ 2 *
      ∫ u : ℝ, Complex.exp (I * (T : ℂ) * u) * g₂ u‖ ≤
        (1 / T ^ 2) * ∫ u : ℝ, ‖g₂ u‖ := by
  have hnorm : ‖(I * (T : ℂ))⁻¹ ^ 2‖ = 1 / T ^ 2 := by
    simp [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hT, inv_pow]
  rw [norm_mul, hnorm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h := norm_integral_le_integral_norm (μ := volume)
    (fun u : ℝ => Complex.exp (I * (T : ℂ) * u) * g₂ u)
  simpa only [norm_mul, norm_oscillatory_exp, one_mul] using h

/-- The ordinary complement amplitude removed by a scalar cutoff. -/
noncomputable def poleCutoffComplement (χ : ℝ → ℂ) (p : ℂ) (u : ℝ) : ℂ :=
  (1 - χ u) / ((u : ℂ) - p)

/-- Exact localized pole identity. Its error is an integral of the ordinary
second derivative of the removed complement, not an assumed Fourier error. -/
theorem localized_pole_integral_eq (χ : ℝ → ℂ) {p : ℂ} (hp : 0 < p.im)
    (g₁ g₂ : ℝ → ℂ)
    (hd : ∀ u, HasDerivAt (poleCutoffComplement χ p) (g₁ u) u)
    (hd₁ : ∀ u, HasDerivAt g₁ (g₂ u) u) (hg₁ : Integrable g₁) (hg₂ : Integrable g₂)
    (hg : Tendsto (poleCutoffComplement χ p) (Bornology.cobounded ℝ) (𝓝 0))
    (hg' : Tendsto g₁ (Bornology.cobounded ℝ) (𝓝 0))
    {T : ℝ} (hT : 0 < T)
    (hχ : Integrable (fun u : ℝ => χ u * Complex.exp (I * (T : ℂ) * u) / ((u : ℂ) - p))) :
    (∫ u : ℝ, χ u * Complex.exp (I * (T : ℂ) * u) / ((u : ℂ) - p)) =
      (2 * Real.pi : ℂ) * I * Complex.exp (I * (T : ℂ) * p) -
        (I * (T : ℂ))⁻¹ ^ 2 * ∫ u : ℝ, Complex.exp (I * (T : ℂ) * u) * g₂ u := by
  have htail := tendsto_oscillatory_integral_second_derivative
    (poleCutoffComplement χ p) g₁ g₂ hd hd₁ hg₁ hg₂ hg hg' hT.ne'
  have hfull := tendsto_intervalIntegral_cexp_div_pole hp hT
  have hactual := intervalIntegral_tendsto_integral hχ tendsto_neg_atTop_atBot tendsto_id
  have hcont : Continuous (poleCutoffComplement χ p) :=
    continuous_iff_continuousAt.mpr (fun u => (hd u).continuousAt)
  have hctail : Continuous (fun u : ℝ => Complex.exp (I * (T : ℂ) * u) *
      poleCutoffComplement χ p u) := by fun_prop
  have heq (R : ℝ) :
      (∫ u in -R..R, Complex.exp (I * (T : ℂ) * u) / ((u : ℂ) - p)) -
        (∫ u in -R..R, Complex.exp (I * (T : ℂ) * u) * poleCutoffComplement χ p u) =
        ∫ u in -R..R, χ u * Complex.exp (I * (T : ℂ) * u) / ((u : ℂ) - p) := by
    have hsplit : (fun u : ℝ => Complex.exp (I * (T : ℂ) * u) / ((u : ℂ) - p)) =
        (fun u : ℝ => χ u * Complex.exp (I * (T : ℂ) * u) / ((u : ℂ) - p) +
          Complex.exp (I * (T : ℂ) * u) * poleCutoffComplement χ p u) := by
      funext u
      dsimp [poleCutoffComplement]
      ring
    rw [hsplit, intervalIntegral.integral_add hχ.intervalIntegrable
      (hctail.intervalIntegrable (-R) R)]
    abel
  exact tendsto_nhds_unique hactual ((hfull.sub htail).congr heq)

/-- The localization estimate is uniform in all parameters whenever the
ordinary second derivatives have the same `L¹` bound. -/
theorem norm_localized_pole_error_le (χ : ℝ → ℂ) {p : ℂ} (hp : 0 < p.im)
    (g₁ g₂ : ℝ → ℂ)
    (hd : ∀ u, HasDerivAt (poleCutoffComplement χ p) (g₁ u) u)
    (hd₁ : ∀ u, HasDerivAt g₁ (g₂ u) u) (hg₁ : Integrable g₁) (hg₂ : Integrable g₂)
    (hg : Tendsto (poleCutoffComplement χ p) (Bornology.cobounded ℝ) (𝓝 0))
    (hg' : Tendsto g₁ (Bornology.cobounded ℝ) (𝓝 0))
    {T : ℝ} (hT : 0 < T)
    (hχ : Integrable (fun u : ℝ => χ u * Complex.exp (I * (T : ℂ) * u) / ((u : ℂ) - p)))
    (C : ℝ) (hC : (∫ u : ℝ, ‖g₂ u‖) ≤ C) :
    ‖(∫ u : ℝ, χ u * Complex.exp (I * (T : ℂ) * u) / ((u : ℂ) - p)) -
      (2 * Real.pi : ℂ) * I * Complex.exp (I * (T : ℂ) * p)‖ ≤ C / T ^ 2 := by
  rw [localized_pole_integral_eq χ hp g₁ g₂ hd hd₁ hg₁ hg₂ hg hg' hT hχ]
  have heq (A B : ℂ) : A - B - A = -B := by ring
  rw [heq, norm_neg]
  calc
    _ ≤ (1 / T ^ 2) * ∫ u : ℝ, ‖g₂ u‖ := norm_second_derivative_remainder g₂ hT
    _ ≤ (1 / T ^ 2) * C := mul_le_mul_of_nonneg_left hC (by positivity)
    _ = C / T ^ 2 := by ring

/-- The complement support is separated from every pole in the half-core
disk by a fixed fraction of its real coordinate. -/
theorem cutoff_denominator_norm_lower (core : ℝ) {p : ℂ}
    (hp : ‖p‖ ≤ core / 2) (u : ℝ) (hu : core ≤ |u|) :
    |u| / 2 ≤ ‖(u : ℂ) - p‖ := by
  have h := norm_sub_norm_le (u : ℂ) p
  simp only [Complex.norm_real, Real.norm_eq_abs] at h
  linarith

theorem cutoff_denominator_inverse_pow_bound (core : ℝ) (hc : 0 < core) {p : ℂ}
    (hp : ‖p‖ ≤ core / 2) (u : ℝ) (hu : core ≤ |u|) (k : ℕ) :
    ‖((u : ℂ) - p)⁻¹‖ ^ k ≤ (2 / |u|) ^ k := by
  have hu₀ : 0 < |u| := hc.trans_le hu
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [norm_inv]
  calc
    ‖(u : ℂ) - p‖⁻¹ ≤ (|u| / 2)⁻¹ :=
      inv_anti₀ (by positivity) (cutoff_denominator_norm_lower core hp u hu)
    _ = 2 / |u| := by ring

private theorem cutoff_denominator_ne_zero {p : ℂ} (hp : 0 < p.im) (u : ℝ) :
    (u : ℂ) - p ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp at hi
  linarith

/-- Explicit first derivative of the removed pole complement. -/
theorem hasDerivAt_poleCutoffComplement (χ : ℝ → ℂ) {p : ℂ} (hp : 0 < p.im)
    {u : ℝ} {χ₁ : ℂ} (hχ : HasDerivAt χ χ₁ u) :
    HasDerivAt (poleCutoffComplement χ p)
      (-χ₁ / ((u : ℂ) - p) - (1 - χ u) / ((u : ℂ) - p) ^ 2) u := by
  have hden := ((hasDerivAt_id (u : ℂ)).sub_const p).comp_ofReal
  have h := ((hasDerivAt_const u (1 : ℂ)).sub hχ).div hden
    (cutoff_denominator_ne_zero hp u)
  convert h using 1
  · rfl
  · dsimp
    field_simp
    ring

/-- Explicit second derivative, used to establish uniform ordinary `L¹`
bounds from cutoff derivatives and the denominator separation estimates. -/
theorem hasDerivAt_poleCutoffComplement_derivative (χ χ₁ : ℝ → ℂ)
    {p : ℂ} (hp : 0 < p.im) {u : ℝ} {χ₂ : ℂ}
    (hχ : HasDerivAt χ (χ₁ u) u) (hχ₁ : HasDerivAt χ₁ χ₂ u) :
    HasDerivAt (fun v : ℝ => -χ₁ v / ((v : ℂ) - p) -
        (1 - χ v) / ((v : ℂ) - p) ^ 2)
      (-χ₂ / ((u : ℂ) - p) + 2 * χ₁ u / ((u : ℂ) - p) ^ 2 +
        2 * (1 - χ u) / ((u : ℂ) - p) ^ 3) u := by
  have hden := ((hasDerivAt_id (u : ℂ)).sub_const p).comp_ofReal
  have hn := cutoff_denominator_ne_zero hp u
  have h := (hχ₁.neg.div hden hn).sub
    (((hasDerivAt_const u (1 : ℂ)).sub hχ).div (hden.pow 2) (pow_ne_zero 2 hn))
  convert h using 1
  · rfl
  · dsimp
    field_simp
    ring

/-- A continuous compactly supported cutoff gives an ordinary integrable
localized pole kernel. -/
theorem integrable_localized_pole (χ : ℝ → ℂ) (hχ : Continuous χ)
    (hs : HasCompactSupport χ) {p : ℂ} (hp : 0 < p.im) (T : ℝ) :
    Integrable (fun u : ℝ => χ u * Complex.exp (I * (T : ℂ) * u) / ((u : ℂ) - p)) := by
  have hc : Continuous (fun u : ℝ => χ u * Complex.exp (I * (T : ℂ) * u) /
      ((u : ℂ) - p)) := by
    apply Continuous.div
    · fun_prop
    · fun_prop
    · exact cutoff_denominator_ne_zero hp
  apply hc.integrable_of_hasCompactSupport
  have hs' := hs.mul_right (f' := fun u : ℝ => Complex.exp (I * (T : ℂ) * u) /
    ((u : ℂ) - p))
  change HasCompactSupport (fun u : ℝ => χ u *
    (Complex.exp (I * (T : ℂ) * u) / ((u : ℂ) - p))) at hs'
  simpa only [Pi.mul_apply, mul_div_assoc] using hs'

theorem compact_cutoff_eventually_zero (χ : ℝ → ℂ) (hs : HasCompactSupport χ) :
    χ =ᶠ[Bornology.cobounded ℝ] 0 := by
  rw [Metric.cobounded_eq_cocompact]
  simpa only [coclosedCompact_eq_cocompact] using hasCompactSupport_iff_eventuallyEq.mp hs

/-- Compact support of the cutoff supplies the first boundary limit in the
localization theorem. -/
theorem tendsto_poleCutoffComplement_zero (χ : ℝ → ℂ) (hs : HasCompactSupport χ) (p : ℂ) :
    Tendsto (poleCutoffComplement χ p) (Bornology.cobounded ℝ) (𝓝 0) := by
  have hi : Tendsto (fun u : ℝ => ((u : ℂ) - p)⁻¹) (Bornology.cobounded ℝ) (𝓝 0) :=
    tendsto_inv₀_cobounded.comp ((tendsto_sub_const_cobounded p).comp
      (RCLike.tendsto_ofReal_cobounded_cobounded ℂ))
  apply hi.congr'
  filter_upwards [compact_cutoff_eventually_zero χ hs] with u hu
  simp [poleCutoffComplement, hu]

/-- Compact support of the cutoff and its first derivative supplies the
second boundary limit in the localization theorem. -/
theorem tendsto_poleCutoffComplement_derivative_zero (χ χ₁ : ℝ → ℂ)
    (hs : HasCompactSupport χ) (hs₁ : HasCompactSupport χ₁) (p : ℂ) :
    Tendsto (fun u : ℝ => -χ₁ u / ((u : ℂ) - p) -
      (1 - χ u) / ((u : ℂ) - p) ^ 2) (Bornology.cobounded ℝ) (𝓝 0) := by
  have hi : Tendsto (fun u : ℝ => ((u : ℂ) - p)⁻¹) (Bornology.cobounded ℝ) (𝓝 0) :=
    tendsto_inv₀_cobounded.comp ((tendsto_sub_const_cobounded p).comp
      (RCLike.tendsto_ofReal_cobounded_cobounded ℂ))
  have h := (hi.pow 2).neg
  simp only [zero_pow (by decide : 2 ≠ 0), neg_zero] at h
  apply h.congr'
  filter_upwards [compact_cutoff_eventually_zero χ hs,
    compact_cutoff_eventually_zero χ₁ hs₁] with u hu hu₁
  simp [hu, hu₁, inv_pow]

theorem cutoff_derivative_zero_in_core (χ χ₁ : ℝ → ℂ)
    (hcore : ∀ u, |u| < 1 → χ u = 1)
    (hd : ∀ u, HasDerivAt χ (χ₁ u) u) {u : ℝ} (hu : |u| < 1) : χ₁ u = 0 := by
  have he : χ =ᶠ[𝓝 u] (fun _ => 1) := by
    filter_upwards [continuous_abs.continuousAt.eventually (gt_mem_nhds hu)] with v hv
    exact hcore v hv
  exact (hd u).unique ((hasDerivAt_const u (1 : ℂ)).congr_of_eventuallyEq he)

theorem cutoff_second_derivative_zero_in_core (χ χ₁ χ₂ : ℝ → ℂ)
    (hcore : ∀ u, |u| < 1 → χ u = 1)
    (hd : ∀ u, HasDerivAt χ (χ₁ u) u) (hd₁ : ∀ u, HasDerivAt χ₁ (χ₂ u) u)
    {u : ℝ} (hu : |u| < 1) : χ₂ u = 0 := by
  have he : χ₁ =ᶠ[𝓝 u] (fun _ => 0) := by
    filter_upwards [continuous_abs.continuousAt.eventually (gt_mem_nhds hu)] with v hv
    exact cutoff_derivative_zero_in_core χ χ₁ hcore hd hv
  exact (hd₁ u).unique ((hasDerivAt_const u (0 : ℂ)).congr_of_eventuallyEq he)

/-- Uniform inverse-denominator estimates outside the unit core. -/
theorem unit_core_inverse_bounds {p : ℂ} (hp : ‖p‖ ≤ 1 / 2) (u : ℝ) (hu : 1 ≤ |u|) :
    ‖((u : ℂ) - p)⁻¹‖ ≤ 2 ∧
      ‖((u : ℂ) - p)⁻¹‖ ^ 2 ≤ 4 ∧
      ‖((u : ℂ) - p)⁻¹‖ ^ 2 ≤ 8 / (1 + u ^ 2) ∧
      ‖((u : ℂ) - p)⁻¹‖ ^ 3 ≤ 16 / (1 + u ^ 2) := by
  have hu₀ : 0 < |u| := by linarith
  have hden : 0 < 1 + u ^ 2 := by positivity
  have h := cutoff_denominator_inverse_pow_bound 1 (by norm_num) hp u hu 1
  simp only [pow_one] at h
  have h₂ : ‖((u : ℂ) - p)⁻¹‖ ≤ 2 := by
    apply h.trans
    exact (div_le_iff₀ hu₀).2 (by linarith)
  have hsq : ‖((u : ℂ) - p)⁻¹‖ ^ 2 ≤ 4 := by
    nlinarith [norm_nonneg (((u : ℂ) - p)⁻¹)]
  have hinv : ‖((u : ℂ) - p)⁻¹‖ ^ 2 ≤ 8 / (1 + u ^ 2) := by
    have hpow := cutoff_denominator_inverse_pow_bound 1 (by norm_num) hp u hu 2
    apply hpow.trans
    apply (le_div_iff₀ hden).2
    have hs : |u| ^ 2 = u ^ 2 := sq_abs u
    have hu₂ : 0 < |u| ^ 2 := pow_pos hu₀ 2
    field_simp
    nlinarith
  refine ⟨h₂, hsq, hinv, ?_⟩
  calc
    _ ≤ 2 * ‖((u : ℂ) - p)⁻¹‖ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right h₂ (sq_nonneg ‖((u : ℂ) - p)⁻¹‖)]
    _ ≤ 2 * (8 / (1 + u ^ 2)) := mul_le_mul_of_nonneg_left hinv (by norm_num)
    _ = _ := by ring

/-- Compact support supplies a finite bound for the derivative weighted by
the integrable Cauchy denominator. -/
theorem exists_weighted_cutoff_bound (f : ℝ → ℂ) (hc : Continuous f)
    (hs : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u, ‖f u‖ ≤ C / (1 + u ^ 2) := by
  let q : ℝ → ℂ := fun u => ((1 + u ^ 2 : ℝ) : ℂ) * f u
  have hqc : Continuous q := by dsimp [q]; fun_prop
  have hqs : HasCompactSupport q := hs.mul_left
  obtain ⟨C, hC⟩ := hqs.exists_bound_of_continuous hqc
  have hC₀ : 0 ≤ C := (norm_nonneg (q 0)).trans (hC 0)
  refine ⟨C, hC₀, fun u => ?_⟩
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 1 + u ^ 2)).2
  have h := hC u
  have hn : ‖((1 + u ^ 2 : ℝ) : ℂ)‖ = 1 + u ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  simpa only [q, norm_mul, hn, mul_comm] using h

theorem unit_cutoff_complement_bounds (χ χ₁ χ₂ : ℝ → ℂ)
    (hcore : ∀ u, |u| < 1 → χ u = 1 ∧ χ₁ u = 0 ∧ χ₂ u = 0)
    (C₀ C₁ C₂ : ℝ) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (h₀ : ∀ u, ‖χ u‖ ≤ C₀)
    (h₁ : ∀ u, ‖χ₁ u‖ ≤ C₁ / (1 + u ^ 2))
    (h₂ : ∀ u, ‖χ₂ u‖ ≤ C₂ / (1 + u ^ 2))
    {p : ℂ} (hp : ‖p‖ ≤ 1 / 2) (u : ℝ) :
    ‖-χ₁ u / ((u : ℂ) - p) - (1 - χ u) / ((u : ℂ) - p) ^ 2‖ ≤
      (2 * C₁ + 8 * (1 + C₀)) / (1 + u ^ 2) ∧
    ‖-χ₂ u / ((u : ℂ) - p) + 2 * χ₁ u / ((u : ℂ) - p) ^ 2 +
        2 * (1 - χ u) / ((u : ℂ) - p) ^ 3‖ ≤
      (2 * C₂ + 8 * C₁ + 32 * (1 + C₀)) / (1 + u ^ 2) := by
  by_cases hu : |u| < 1
  · obtain ⟨he, he₁, he₂⟩ := hcore u hu
    simp only [he, he₁, he₂, neg_zero, zero_div, sub_self, mul_zero,
      add_zero, norm_zero]
    constructor <;> positivity
  · obtain ⟨hA, hA₂, hA₂', hA₃⟩ := unit_core_inverse_bounds hp u (le_of_not_gt hu)
    have hone : ‖1 - χ u‖ ≤ 1 + C₀ := by
      calc
        _ ≤ ‖(1 : ℂ)‖ + ‖χ u‖ := norm_sub_le _ _
        _ ≤ 1 + C₀ := by simpa using add_le_add_left (h₀ u) 1
    have hfirst : ‖-χ₁ u / ((u : ℂ) - p) - (1 - χ u) / ((u : ℂ) - p) ^ 2‖ ≤
        ‖χ₁ u‖ * ‖((u : ℂ) - p)⁻¹‖ + ‖1 - χ u‖ * ‖((u : ℂ) - p)⁻¹‖ ^ 2 := by
      calc
        _ ≤ ‖-χ₁ u / ((u : ℂ) - p)‖ + ‖(1 - χ u) / ((u : ℂ) - p) ^ 2‖ :=
          norm_sub_le _ _
        _ = _ := by rw [norm_div, norm_neg, norm_div, norm_pow]; simp [norm_inv, div_eq_mul_inv, inv_pow]
    have hsecond : ‖-χ₂ u / ((u : ℂ) - p) + 2 * χ₁ u / ((u : ℂ) - p) ^ 2 +
        2 * (1 - χ u) / ((u : ℂ) - p) ^ 3‖ ≤
        ‖χ₂ u‖ * ‖((u : ℂ) - p)⁻¹‖ +
          2 * ‖χ₁ u‖ * ‖((u : ℂ) - p)⁻¹‖ ^ 2 +
          2 * ‖1 - χ u‖ * ‖((u : ℂ) - p)⁻¹‖ ^ 3 := by
      have h := (norm_add_le (-χ₂ u / ((u : ℂ) - p) + 2 * χ₁ u / ((u : ℂ) - p) ^ 2)
        (2 * (1 - χ u) / ((u : ℂ) - p) ^ 3)).trans
        (add_le_add (norm_add_le (-χ₂ u / ((u : ℂ) - p))
          (2 * χ₁ u / ((u : ℂ) - p) ^ 2)) le_rfl)
      simpa [norm_div, norm_neg, norm_mul, norm_pow, norm_inv, div_eq_mul_inv, inv_pow] using h
    constructor
    · calc
        _ ≤ ‖χ₁ u‖ * ‖((u : ℂ) - p)⁻¹‖ + ‖1 - χ u‖ * ‖((u : ℂ) - p)⁻¹‖ ^ 2 := hfirst
        _ ≤ (C₁ / (1 + u ^ 2)) * 2 + (1 + C₀) * (8 / (1 + u ^ 2)) := by
          gcongr
          exact h₁ u
        _ = _ := by ring
    · calc
        _ ≤ ‖χ₂ u‖ * ‖((u : ℂ) - p)⁻¹‖ +
          2 * ‖χ₁ u‖ * ‖((u : ℂ) - p)⁻¹‖ ^ 2 +
          2 * ‖1 - χ u‖ * ‖((u : ℂ) - p)⁻¹‖ ^ 3 := hsecond
        _ ≤ (C₂ / (1 + u ^ 2)) * 2 +
          2 * (C₁ / (1 + u ^ 2)) * 4 + 2 * (1 + C₀) * (16 / (1 + u ^ 2)) := by
          gcongr
          all_goals first | exact h₂ u | exact h₁ u
        _ = _ := by ring

/-- Automatic uniform localization for a fixed twice continuously
differentiable compactly supported cutoff equal to one on the unit core.
All complement integrability, endpoint decay, and uniform `L¹` bounds are
derived here from the ordinary cutoff data. -/
theorem exists_uniform_localized_pole_bound (χ χ₁ χ₂ : ℝ → ℂ)
    (hd : ∀ u, HasDerivAt χ (χ₁ u) u) (hd₁ : ∀ u, HasDerivAt χ₁ (χ₂ u) u)
    (hc₂ : Continuous χ₂) (hs : HasCompactSupport χ)
    (hcore : ∀ u, |u| < 1 → χ u = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℂ, 0 < p.im → ‖p‖ ≤ 1 / 2 → ∀ T : ℝ, 0 < T →
      ‖(∫ u : ℝ, χ u * Complex.exp (I * (T : ℂ) * u) / ((u : ℂ) - p)) -
        (2 * Real.pi : ℂ) * I * Complex.exp (I * (T : ℂ) * p)‖ ≤ C / T ^ 2 := by
  have hc : Continuous χ := continuous_iff_continuousAt.mpr (fun u => (hd u).continuousAt)
  have hc₁ : Continuous χ₁ := continuous_iff_continuousAt.mpr (fun u => (hd₁ u).continuousAt)
  have hs₁ : HasCompactSupport χ₁ := by
    have heq : χ₁ = deriv χ := funext (fun u => (hd u).deriv.symm)
    rw [heq]
    exact hs.deriv
  have hs₂ : HasCompactSupport χ₂ := by
    have heq : χ₂ = deriv χ₁ := funext (fun u => (hd₁ u).deriv.symm)
    rw [heq]
    exact hs₁.deriv
  obtain ⟨C₀, h₀⟩ := hs.exists_bound_of_continuous hc
  have hC₀ : 0 ≤ C₀ := (norm_nonneg (χ 0)).trans (h₀ 0)
  obtain ⟨C₁, hC₁, h₁⟩ := exists_weighted_cutoff_bound χ₁ hc₁ hs₁
  obtain ⟨C₂, hC₂, h₂⟩ := exists_weighted_cutoff_bound χ₂ hc₂ hs₂
  let A₁ := 2 * C₁ + 8 * (1 + C₀)
  let A₂ := 2 * C₂ + 8 * C₁ + 32 * (1 + C₀)
  have hA₁ : 0 ≤ A₁ := by dsimp [A₁]; positivity
  have hA₂ : 0 ≤ A₂ := by dsimp [A₂]; positivity
  refine ⟨A₂ * Real.pi, mul_nonneg hA₂ Real.pi_pos.le, ?_⟩
  intro p hp hp' T hT
  let g₁ : ℝ → ℂ := fun u => -χ₁ u / ((u : ℂ) - p) - (1 - χ u) / ((u : ℂ) - p) ^ 2
  let g₂ : ℝ → ℂ := fun u => -χ₂ u / ((u : ℂ) - p) + 2 * χ₁ u / ((u : ℂ) - p) ^ 2 +
    2 * (1 - χ u) / ((u : ℂ) - p) ^ 3
  have hvals : ∀ u, |u| < 1 → χ u = 1 ∧ χ₁ u = 0 ∧ χ₂ u = 0 := by
    intro u hu
    exact ⟨hcore u hu, cutoff_derivative_zero_in_core χ χ₁ hcore hd hu,
      cutoff_second_derivative_zero_in_core χ χ₁ χ₂ hcore hd hd₁ hu⟩
  have hb : ∀ u, ‖g₁ u‖ ≤ A₁ / (1 + u ^ 2) ∧ ‖g₂ u‖ ≤ A₂ / (1 + u ^ 2) :=
    unit_cutoff_complement_bounds χ χ₁ χ₂ hvals C₀ C₁ C₂ hC₀ hC₁ hC₂ h₀ h₁ h₂ hp'
  have hn : ∀ u : ℝ, (u : ℂ) - p ≠ 0 := cutoff_denominator_ne_zero hp
  have hcg₁ : Continuous g₁ := by dsimp [g₁]; fun_prop (disch := aesop)
  have hcg₂ : Continuous g₂ := by dsimp [g₂]; fun_prop (disch := aesop)
  have hmaj₁ : Integrable (fun u : ℝ => A₁ / (1 + u ^ 2)) := by
    simpa only [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul A₁
  have hmaj₂ : Integrable (fun u : ℝ => A₂ / (1 + u ^ 2)) := by
    simpa only [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul A₂
  have hig₁ : Integrable g₁ := hmaj₁.mono' hcg₁.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun u => (hb u).1))
  have hig₂ : Integrable g₂ := hmaj₂.mono' hcg₂.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun u => (hb u).2))
  have hL : (∫ u : ℝ, ‖g₂ u‖) ≤ A₂ * Real.pi := by
    calc
      _ ≤ ∫ u : ℝ, A₂ / (1 + u ^ 2) := integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun u => norm_nonneg (g₂ u))) hmaj₂
        (Filter.Eventually.of_forall (fun u => (hb u).2))
      _ = _ := by simp [div_eq_mul_inv, integral_const_mul, integral_univ_inv_one_add_sq]
  exact norm_localized_pole_error_le χ hp g₁ g₂
    (fun u => hasDerivAt_poleCutoffComplement χ hp (hd u))
    (fun u => hasDerivAt_poleCutoffComplement_derivative χ χ₁ hp (hd u) (hd₁ u))
    hig₁ hig₂ (tendsto_poleCutoffComplement_zero χ hs p)
    (tendsto_poleCutoffComplement_derivative_zero χ χ₁ hs hs₁ p) hT
    (integrable_localized_pole χ hc hs hp T) (A₂ * Real.pi) hL

/-- A fixed real smooth cutoff: one on the closed unit interval and zero
outside the open interval of radius two. -/
def unitPoleBump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

noncomputable def unitPoleCutoff : ℝ → ℝ := unitPoleBump

theorem unitPoleCutoff_contDiff : ContDiff ℝ ∞ unitPoleCutoff :=
  unitPoleBump.contDiff

theorem unitPoleCutoff_hasCompactSupport : HasCompactSupport unitPoleCutoff :=
  unitPoleBump.hasCompactSupport

theorem unitPoleCutoff_eq_one {u : ℝ} (hu : |u| ≤ 1) : unitPoleCutoff u = 1 := by
  apply unitPoleBump.one_of_mem_closedBall
  simpa [Metric.mem_closedBall, Real.dist_eq, unitPoleBump] using hu

theorem unitPoleCutoff_eq_zero {u : ℝ} (hu : 2 ≤ |u|) : unitPoleCutoff u = 0 := by
  apply unitPoleBump.zero_of_le_dist
  simpa [Real.dist_eq, unitPoleBump] using hu

theorem unitPoleCutoff_mem_Icc (u : ℝ) : unitPoleCutoff u ∈ Icc (0 : ℝ) 1 :=
  ⟨unitPoleBump.nonneg, unitPoleBump.le_one⟩

/-- The concrete smooth real cutoff has a uniform quadratic localization
remainder for every upper-half-plane pole in the half-unit ball. -/
theorem exists_uniform_unitPoleCutoff_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℂ, 0 < p.im → ‖p‖ ≤ 1 / 2 → ∀ T : ℝ, 0 < T →
      ‖(∫ u : ℝ, (unitPoleCutoff u : ℂ) * Complex.exp (I * (T : ℂ) * u) /
          ((u : ℂ) - p)) -
        (2 * Real.pi : ℂ) * I * Complex.exp (I * (T : ℂ) * p)‖ ≤ C / T ^ 2 := by
  let χ : ℝ → ℂ := fun u => (unitPoleCutoff u : ℂ)
  have hc : ContDiff ℝ ∞ χ := Complex.ofRealCLM.contDiff.comp unitPoleCutoff_contDiff
  obtain ⟨hd, hc₁⟩ := contDiff_infty_iff_deriv.mp hc
  obtain ⟨hd₁, hc₂⟩ := contDiff_infty_iff_deriv.mp hc₁
  apply exists_uniform_localized_pole_bound χ (deriv χ) (deriv (deriv χ))
    (fun u => (hd u).hasDerivAt) (fun u => (hd₁ u).hasDerivAt) hc₂.continuous
  · exact unitPoleCutoff_hasCompactSupport.comp_left Complex.ofReal_zero
  · intro u hu
    simp only [χ, unitPoleCutoff_eq_one hu.le, Complex.ofReal_one]

/-- The same normal cutoff may be placed in an arbitrarily small local
analytic chart by scaling its real argument. -/
noncomputable def scaledPoleCutoff (ρ : ℝ) (u : ℝ) : ℝ := unitPoleCutoff (u / ρ)

theorem integral_scaledPoleCutoff {ρ : ℝ} (hρ : 0 < ρ) (p : ℂ) (T : ℝ) :
    (∫ u : ℝ, (scaledPoleCutoff ρ u : ℂ) * Complex.exp (I * (T : ℂ) * u) /
      ((u : ℂ) - p)) =
    ∫ u : ℝ, (unitPoleCutoff u : ℂ) * Complex.exp (I * ((T * ρ : ℝ) : ℂ) * u) /
      ((u : ℂ) - p / (ρ : ℂ)) := by
  let f : ℝ → ℂ := fun u => (scaledPoleCutoff ρ u : ℂ) *
    Complex.exp (I * (T : ℂ) * u) / ((u : ℂ) - p)
  have hρc : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ.ne'
  have he (u : ℝ) : f (ρ * u) = (ρ : ℂ)⁻¹ *
      ((unitPoleCutoff u : ℂ) * Complex.exp (I * ((T * ρ : ℝ) : ℂ) * u) /
        ((u : ℂ) - p / (ρ : ℂ))) := by
    dsimp [f, scaledPoleCutoff]
    rw [mul_div_cancel_left₀ u hρ.ne']
    push_cast
    have hexp : I * (T : ℂ) * ((ρ : ℂ) * u) = I * ((T : ℂ) * ρ) * u := by ring
    rw [hexp]
    rw [show (ρ : ℂ) * u - p = (ρ : ℂ) * ((u : ℂ) - p / (ρ : ℂ)) by
      field_simp]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hscale := Measure.integral_comp_mul_left f ρ
  simp_rw [he] at hscale
  rw [integral_const_mul, abs_of_pos (inv_pos.mpr hρ),
    Complex.real_smul, Complex.ofReal_inv] at hscale
  exact mul_left_cancel₀ (inv_ne_zero hρc) hscale.symm

theorem scaledPoleCutoff_eq_one {ρ u : ℝ} (hρ : 0 < ρ) (hu : |u| ≤ ρ) :
    scaledPoleCutoff ρ u = 1 := by
  apply unitPoleCutoff_eq_one
  rw [abs_div, abs_of_pos hρ]
  exact (div_le_one hρ).mpr hu

theorem scaledPoleCutoff_eq_zero {ρ u : ℝ} (hρ : 0 < ρ) (hu : 2 * ρ ≤ |u|) :
    scaledPoleCutoff ρ u = 0 := by
  apply unitPoleCutoff_eq_zero
  rw [abs_div, abs_of_pos hρ]
  exact (le_div_iff₀ hρ).mpr hu

/-- Uniform localization at any positive normal-chart scale. The constant
depends only on that scale, and not on the upper-half-plane pole. -/
theorem exists_uniform_scaledPoleCutoff_bound {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℂ, 0 < p.im → ‖p‖ ≤ ρ / 2 → ∀ T : ℝ, 0 < T →
      ‖(∫ u : ℝ, (scaledPoleCutoff ρ u : ℂ) * Complex.exp (I * (T : ℂ) * u) /
          ((u : ℂ) - p)) -
        (2 * Real.pi : ℂ) * I * Complex.exp (I * (T : ℂ) * p)‖ ≤ C / T ^ 2 := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_unitPoleCutoff_bound
  refine ⟨C / ρ ^ 2, div_nonneg hC (sq_nonneg _), ?_⟩
  intro p hp hp' T hT
  have hpi : 0 < (p / (ρ : ℂ)).im := by
    rw [Complex.div_ofReal_im]
    exact div_pos hp hρ
  have hpn : ‖p / (ρ : ℂ)‖ ≤ 1 / 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    apply (div_le_iff₀ hρ).mpr
    linarith
  have h := hb (p / (ρ : ℂ)) hpi hpn (T * ρ) (mul_pos hT hρ)
  rw [integral_scaledPoleCutoff hρ]
  have hρc : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ.ne'
  have he : I * ((T * ρ : ℝ) : ℂ) * (p / (ρ : ℂ)) = I * (T : ℂ) * p := by
    push_cast
    field_simp
  rw [he] at h
  exact h.trans_eq (by rw [mul_pow]; ring)

end Maxwell.Green
