import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.RCLike
import Mathlib.Tactic

/-! # The real-line Fourier pole via an absolutely integrable squared pole

The Laplace transform of `t exp(-a t)` is absolutely integrable in the Fourier
variable. Fourier inversion for that function avoids exchanging conditionally
convergent integrals. A subsequent finite-interval integration by parts recovers
the simple pole.
-/

open MeasureTheory Filter Set Complex
open scoped Topology FourierTransform

namespace Maxwell.Green

/-- The first Laplace moment is integrable for a complex coefficient with
positive real part. -/
theorem integrableOn_mul_cexp_neg_mul {a : ℂ} (ha : 0 < a.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) * Complex.exp (-a * t)) (Ioi 0) := by
  have hreal := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := 1) (s := 1) (b := a.re) (by norm_num) (by norm_num) ha
  simp only [Real.rpow_one] at hreal
  apply hreal.mono'
  · exact Continuous.aestronglyMeasurable (by fun_prop)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [mem_Ioi] at ht
    simp [Complex.norm_exp, Complex.mul_re, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht]

/-- Polynomial damping against the positive real part controls the complex
Laplace moment at infinity. -/
theorem tendsto_mul_cexp_neg_mul {a : ℂ} (ha : 0 < a.re) :
    Tendsto (fun t : ℝ => (t : ℂ) * Complex.exp (-a * t)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 : ℝ) a.re ha
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  simp [Complex.norm_exp, Complex.mul_re, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos ht, Real.rpow_one]

/-- The zeroth Laplace factor also tends to zero. -/
theorem tendsto_cexp_neg_mul {a : ℂ} (ha : 0 < a.re) :
    Tendsto (fun t : ℝ => Complex.exp (-a * t)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (0 : ℝ) a.re ha
  simpa [Complex.norm_exp, Complex.mul_re] using h

/-- Exact complex Laplace integral of the first moment. -/
theorem integral_mul_cexp_neg_mul_Ioi {a : ℂ} (ha : 0 < a.re) :
    (∫ t : ℝ in Ioi 0, (t : ℂ) * Complex.exp (-a * t)) = a⁻¹ ^ 2 := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  let F : ℂ → ℂ := fun z => -(z / a + a⁻¹ ^ 2) * Complex.exp (-a * z)
  have hderiv : ∀ z : ℂ, HasDerivAt F (z * Complex.exp (-a * z)) z := by
    intro z
    convert (((hasDerivAt_id z).div_const a).add_const (a⁻¹ ^ 2)).neg.mul
      (((hasDerivAt_id z).const_mul (-a)).cexp) using 1
    · funext w
      dsimp [F]
    · dsimp
      field_simp
      ring
  have hlim : Tendsto (fun t : ℝ => F t) atTop (𝓝 0) := by
    have h₁ := (tendsto_mul_cexp_neg_mul ha).const_mul (-a⁻¹)
    have h₂ := (tendsto_cexp_neg_mul ha).const_mul (-(a⁻¹ ^ 2))
    convert h₁.add h₂ using 1
    · funext t
      dsimp [F]
      ring
    · simp
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (a := (0 : ℝ)) (f := fun t : ℝ => F t)
    (fun t _ => (hderiv t).comp_ofReal)
    (integrableOn_mul_cexp_neg_mul ha) hlim
  simpa [F] using h

/-- The causal first Laplace moment, extended by zero to the real line. -/
noncomputable def positiveLaplaceMoment (a : ℂ) : ℝ → ℂ :=
  (Ioi (0 : ℝ)).indicator (fun t => (t : ℂ) * Complex.exp (-a * t))

theorem integrable_positiveLaplaceMoment {a : ℂ} (ha : 0 < a.re) :
    Integrable (positiveLaplaceMoment a) :=
  (integrable_indicator_iff measurableSet_Ioi).2 (integrableOn_mul_cexp_neg_mul ha)

/-- Fourier transformation of the causal Laplace moment produces an
absolutely integrable squared pole. -/
theorem fourier_positiveLaplaceMoment {a : ℂ} (ha : 0 < a.re) (ξ : ℝ) :
    𝓕 (positiveLaplaceMoment a) ξ = (a + (2 * Real.pi * ξ : ℝ) * I)⁻¹ ^ 2 := by
  have hb : 0 < (a + (2 * Real.pi * ξ : ℝ) * I).re := by simpa using ha
  rw [Real.fourier_eq']
  have heq : (fun t : ℝ => Complex.exp ((↑(-2 * Real.pi * inner ℝ t ξ) * I)) •
      positiveLaplaceMoment a t) =
      (Ioi (0 : ℝ)).indicator
        (fun t => (t : ℂ) * Complex.exp (-(a + (2 * Real.pi * ξ : ℝ) * I) * t)) := by
    funext t
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · simp only [positiveLaplaceMoment, indicator_of_mem ht, smul_eq_mul,
        real_inner_comm, Real.inner_apply]
      calc
        _ = (t : ℂ) * (Complex.exp ((↑(-2 * Real.pi * (ξ * t)) * I)) *
            Complex.exp (-a * t)) := by ring
        _ = _ := by
          rw [← Complex.exp_add]
          congr 2
          push_cast
          ring
    · simp [positiveLaplaceMoment, ht]
  rw [heq, integral_indicator measurableSet_Ioi]
  exact integral_mul_cexp_neg_mul_Ioi hb

theorem continuousAt_positiveLaplaceMoment (a : ℂ) {T : ℝ} (hT : 0 < T) :
    ContinuousAt (positiveLaplaceMoment a) T := by
  have heq : positiveLaplaceMoment a =ᶠ[𝓝 T]
      (fun t : ℝ => (t : ℂ) * Complex.exp (-a * t)) := by
    filter_upwards [Ioi_mem_nhds hT] with t ht
    exact indicator_of_mem ht _
  exact (show ContinuousAt (fun t : ℝ => (t : ℂ) * Complex.exp (-a * t)) T from
    (by fun_prop)).congr_of_eventuallyEq heq

theorem norm_squared_laplace_pole (a : ℂ) (x : ℝ) :
    ‖(a + (2 * Real.pi * x : ℝ) * I)⁻¹ ^ 2‖ =
      (a.re ^ 2 + (a.im + 2 * Real.pi * x) ^ 2)⁻¹ := by
  rw [norm_pow, norm_inv, inv_pow, ← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, pow_two]

theorem integrable_squared_laplace_pole {a : ℂ} (ha : 0 < a.re) :
    Integrable (fun x : ℝ => (a + (2 * Real.pi * x : ℝ) * I)⁻¹ ^ 2) := by
  have hn (x : ℝ) : a + (2 * Real.pi * x : ℝ) * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hc : Continuous (fun x : ℝ => (a + (2 * Real.pi * x : ℝ) * I)⁻¹ ^ 2) := by
    exact ((by fun_prop : Continuous (fun x : ℝ => a +
      (2 * Real.pi * x : ℝ) * I)).inv₀ hn).pow 2
  rw [← integrable_norm_iff hc.aestronglyMeasurable]
  have hh := (((integrable_inv_one_add_sq.comp_div ha.ne').comp_add_left a.im).comp_mul_left'
    (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)).const_mul (a.re ^ 2)⁻¹
  apply hh.congr
  filter_upwards [] with x
  rw [norm_squared_laplace_pole]
  field_simp

/-- Fourier inversion is applicable here because the squared pole is
absolutely integrable. -/
theorem integral_fourier_squared_laplace_pole {a : ℂ} (ha : 0 < a.re)
    {T : ℝ} (hT : 0 < T) :
    (∫ ξ : ℝ, Complex.exp ((2 * Real.pi * (ξ * T) : ℝ) * I) *
      (a + (2 * Real.pi * ξ : ℝ) * I)⁻¹ ^ 2) =
      (T : ℂ) * Complex.exp (-a * T) := by
  have hft : 𝓕 (positiveLaplaceMoment a) =
      (fun ξ : ℝ => (a + (2 * Real.pi * ξ : ℝ) * I)⁻¹ ^ 2) :=
    funext (fourier_positiveLaplaceMoment ha)
  have hfi : Integrable (𝓕 (positiveLaplaceMoment a)) := by
    rw [hft]
    exact integrable_squared_laplace_pole ha
  have h := (integrable_positiveLaplaceMoment ha).fourierInv_fourier_eq hfi
    (continuousAt_positiveLaplaceMoment a hT)
  rw [hft, Real.fourierInv_eq'] at h
  simpa only [Real.inner_apply, smul_eq_mul, positiveLaplaceMoment,
    indicator_of_mem (show T ∈ Ioi (0 : ℝ) from hT)] using h

/-- Removing the Fourier convention's `2π` from the integration variable. -/
theorem integral_scaled_squared_laplace_pole {a : ℂ} (ha : 0 < a.re)
    {T : ℝ} (hT : 0 < T) :
    (∫ u : ℝ, Complex.exp ((u * T : ℝ) * I) * (a + (u : ℂ) * I)⁻¹ ^ 2) =
      (2 * Real.pi : ℂ) * ((T : ℂ) * Complex.exp (-a * T)) := by
  let g : ℝ → ℂ := fun u => Complex.exp ((u * T : ℝ) * I) * (a + (u : ℂ) * I)⁻¹ ^ 2
  have hleft : (∫ ξ : ℝ, g (2 * Real.pi * ξ)) =
      (T : ℂ) * Complex.exp (-a * T) := by
    simpa only [g, mul_assoc] using integral_fourier_squared_laplace_pole ha hT
  have hscale := Measure.integral_comp_mul_left g (2 * Real.pi)
  have hπ : 0 < 2 * Real.pi := by positivity
  rw [hleft, abs_of_pos (inv_pos.mpr hπ), Complex.real_smul, Complex.ofReal_inv] at hscale
  have hπc : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hπ.ne'
  have h := congrArg (fun z : ℂ => ((2 * Real.pi : ℝ) : ℂ) * z) hscale
  simp only [← mul_assoc, mul_inv_cancel₀ hπc, one_mul] at h
  simpa only [g, Complex.ofReal_mul, Complex.ofReal_ofNat, ← mul_assoc] using h.symm

/-- The upper-half-plane squared-pole Fourier identity, obtained from
absolutely convergent Fourier inversion rather than a residue assumption. -/
theorem integral_cexp_div_sq_pole {p : ℂ} (hp : 0 < p.im) {T : ℝ} (hT : 0 < T) :
    (∫ u : ℝ, Complex.exp (I * (T : ℂ) * u) / ((u : ℂ) - p) ^ 2) =
      -(2 * Real.pi : ℂ) * (T : ℂ) * Complex.exp (I * (T : ℂ) * p) := by
  have ha : 0 < (-I * p).re := by simpa using hp
  have h := integral_scaled_squared_laplace_pole ha hT
  have heq : (fun u : ℝ => Complex.exp ((u * T : ℝ) * I) *
      (-I * p + (u : ℂ) * I)⁻¹ ^ 2) =
      (fun u : ℝ => -(Complex.exp (I * (T : ℂ) * u) / ((u : ℂ) - p) ^ 2)) := by
    funext u
    have hpole : -I * p + (u : ℂ) * I = I * ((u : ℂ) - p) := by ring
    have hexp : ((u * T : ℝ) : ℂ) * I = I * (T : ℂ) * u := by push_cast; ring
    rw [hpole, hexp, mul_inv_rev, mul_pow]
    simp [Complex.inv_I, div_eq_mul_inv]
  rw [heq, integral_neg] at h
  have hexp : -(-I * p) * (T : ℂ) = I * (T : ℂ) * p := by ring
  rw [hexp] at h
  linear_combination -h

theorem integrable_cexp_div_sq_pole {p : ℂ} (hp : 0 < p.im) {T : ℝ} (hT : 0 < T) :
    Integrable (fun u : ℝ => Complex.exp (I * (T : ℂ) * u) / ((u : ℂ) - p) ^ 2) := by
  apply Integrable.of_integral_ne_zero
  simp [integral_cexp_div_sq_pole hp hT, hT.ne', Real.pi_ne_zero]

theorem tendsto_intervalIntegral_cexp_div_sq_pole {p : ℂ} (hp : 0 < p.im)
    {T : ℝ} (hT : 0 < T) :
    Tendsto (fun R : ℝ => ∫ u in -R..R,
      Complex.exp (I * (T : ℂ) * u) / ((u : ℂ) - p) ^ 2) atTop
      (𝓝 (-(2 * Real.pi : ℂ) * (T : ℂ) * Complex.exp (I * (T : ℂ) * p))) := by
  have h := intervalIntegral_tendsto_integral (integrable_cexp_div_sq_pole hp hT)
    tendsto_neg_atTop_atBot tendsto_id
  rwa [integral_cexp_div_sq_pole hp hT] at h

private theorem real_sub_pole_ne_zero {p : ℂ} (hp : 0 < p.im) (u : ℝ) :
    (u : ℂ) - p ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp at hi
  linarith

theorem hasDerivAt_pole_boundary {p : ℂ} (hp : 0 < p.im) (T u : ℝ) :
    HasDerivAt (fun v : ℝ => Complex.exp (I * T * v) / ((v : ℂ) - p))
      (I * T * (Complex.exp (I * T * u) / ((u : ℂ) - p)) -
        Complex.exp (I * T * u) / ((u : ℂ) - p) ^ 2) u := by
  have h := (((hasDerivAt_id (u : ℂ)).const_mul (I * T)).cexp).div
    ((hasDerivAt_id (u : ℂ)).sub_const p) (real_sub_pole_ne_zero hp u)
  convert h.comp_ofReal using 1
  · rfl
  · dsimp
    field_simp [real_sub_pole_ne_zero hp u]

/-- Finite-interval integration by parts relates the conditionally integrable
simple pole to the absolutely integrable squared pole. -/
theorem simple_pole_finite_interval {p : ℂ} (hp : 0 < p.im) {T : ℝ} (hT : T ≠ 0)
    (a b : ℝ) :
    (∫ u : ℝ in a..b, Complex.exp (I * T * u) / ((u : ℂ) - p)) =
    (I * T)⁻¹ *
      (Complex.exp (I * T * b) / ((b : ℂ) - p) -
       Complex.exp (I * T * a) / ((a : ℂ) - p) +
       ∫ u : ℝ in a..b, Complex.exp (I * T * u) / ((u : ℂ) - p) ^ 2) := by
  have hc₁ : Continuous (fun u : ℝ => Complex.exp (I * T * u) / ((u : ℂ) - p)) := by
    apply Continuous.div
    · fun_prop
    · fun_prop
    · exact real_sub_pole_ne_zero hp
  have hc₂ : Continuous (fun u : ℝ => Complex.exp (I * T * u) / ((u : ℂ) - p) ^ 2) := by
    apply Continuous.div
    · fun_prop
    · fun_prop
    · exact fun u => pow_ne_zero 2 (real_sub_pole_ne_zero hp u)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => hasDerivAt_pole_boundary hp T u)
    (((hc₁.const_mul (I * (T : ℂ))).sub hc₂).intervalIntegrable a b)
  rw [intervalIntegral.integral_sub
      ((hc₁.const_mul (I * (T : ℂ))).intervalIntegrable a b) (hc₂.intervalIntegrable a b),
    intervalIntegral.integral_const_mul] at h
  have hiT : I * (T : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hT)
  apply (mul_left_cancel₀ hiT)
  rw [← mul_assoc, mul_inv_cancel₀ hiT, one_mul]
  exact sub_eq_iff_eq_add.mp h

theorem tendsto_pole_boundary_zero (p : ℂ) (T : ℝ) :
    Tendsto (fun u : ℝ => Complex.exp (I * T * u) / ((u : ℂ) - p))
      (Bornology.cobounded ℝ) (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hi : Tendsto (fun u : ℝ => ((u : ℂ) - p)⁻¹) (Bornology.cobounded ℝ) (𝓝 0) :=
    tendsto_inv₀_cobounded.comp ((tendsto_sub_const_cobounded p).comp
      (RCLike.tendsto_ofReal_cobounded_cobounded ℂ))
  convert hi.norm using 1
  · ext u
    simp [Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  · simp

theorem tendsto_pole_boundary_pos_zero (p : ℂ) (T : ℝ) :
    Tendsto (fun R : ℝ => Complex.exp (I * T * R) / ((R : ℂ) - p))
      atTop (𝓝 0) :=
  (tendsto_pole_boundary_zero p T).mono_left IsOrderBornology.atTop_le_cobounded

theorem tendsto_pole_boundary_neg_zero (p : ℂ) (T : ℝ) :
    Tendsto (fun R : ℝ => Complex.exp (I * (T : ℂ) * ((-R : ℝ) : ℂ)) /
      (((-R : ℝ) : ℂ) - p)) atTop (𝓝 0) := by
  have hb : Tendsto (fun u : ℝ => Complex.exp (I * T * u) / ((u : ℂ) - p))
      atBot (𝓝 0) :=
    (tendsto_pole_boundary_zero p T).mono_left IsOrderBornology.atBot_le_cobounded
  exact hb.comp tendsto_neg_atTop_atBot

/-- The genuine improper Fourier simple-pole identity in the upper half
plane. The limit is derived from the squared-pole integral and vanishing
finite-interval boundary terms. -/
theorem tendsto_intervalIntegral_cexp_div_pole {p : ℂ} (hp : 0 < p.im)
    {T : ℝ} (hT : 0 < T) :
    Tendsto (fun R : ℝ => ∫ u in -R..R,
      Complex.exp (I * (T : ℂ) * u) / ((u : ℂ) - p)) atTop
      (𝓝 ((2 * Real.pi : ℂ) * I * Complex.exp (I * (T : ℂ) * p))) := by
  have h := (((tendsto_pole_boundary_pos_zero p T).sub
    (tendsto_pole_boundary_neg_zero p T)).add
      (tendsto_intervalIntegral_cexp_div_sq_pole hp hT)).const_mul (I * (T : ℂ))⁻¹
  have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hv : (I * (T : ℂ))⁻¹ *
      (0 - 0 + -(2 * Real.pi : ℂ) * (T : ℂ) * Complex.exp (I * (T : ℂ) * p)) =
      (2 * Real.pi : ℂ) * I * Complex.exp (I * (T : ℂ) * p) := by
    rw [mul_inv_rev, Complex.inv_I]
    simp only [sub_self, zero_add]
    field_simp
  rw [hv] at h
  exact h.congr (fun R => (simple_pole_finite_interval hp hT.ne' (-R) R).symm)

end Maxwell.Green
