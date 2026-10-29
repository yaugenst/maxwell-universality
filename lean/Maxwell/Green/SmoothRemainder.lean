import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Maxwell.Green.PoleCutoff

/-! # Polynomial decay of the smooth periodic remainder

Two integrations by parts suffice for the three-dimensional leading
`T⁻¹` term and `T⁻³ᐟ²` error. The estimate is for the already-shifted
integral, so multiplying it by the contour exponential preserves that factor.
-/

open MeasureTheory Set Complex

noncomputable section

namespace Maxwell.Green

def oscillatoryFactor (T x : ℝ) : ℂ := Complex.exp (Complex.I * T * x)

theorem oscillatoryFactor_hasDerivAt (T x : ℝ) :
    HasDerivAt (oscillatoryFactor T) (Complex.I * T * oscillatoryFactor T x) x := by
  convert (((hasDerivAt_id (x : ℂ)).const_mul (Complex.I * T)).cexp).comp_ofReal using 1
  · rfl
  · dsimp [oscillatoryFactor]
    ring

theorem oscillatoryFactor_norm (T x : ℝ) : ‖oscillatoryFactor T x‖ = 1 := by
  simp [oscillatoryFactor, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem oscillatoryFactor_integer_period (n : ℤ) (x : ℝ) :
    oscillatoryFactor n (x + 2 * Real.pi) = oscillatoryFactor n x := by
  unfold oscillatoryFactor
  push_cast
  have harg : Complex.I * (n : ℂ) * ((x + 2 * Real.pi : ℝ) : ℂ) =
      Complex.I * (n : ℂ) * x + (n : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  push_cast at harg
  rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- One integration by parts for a periodic amplitude on a full period. -/
theorem periodic_fourier_derivative
    {f f' : ℝ → ℂ} {a b T : ℝ}
    (hf : ∀ x ∈ uIcc a b, HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume a b)
    (hperiod : f b = f a)
    (hphase : oscillatoryFactor T b = oscillatoryFactor T a) :
    (∫ x in a..b, oscillatoryFactor T x * f' x) =
      -(Complex.I * T) * (∫ x in a..b, oscillatoryFactor T x * f x) := by
  have he : Continuous (oscillatoryFactor T) := by
    exact continuous_iff_continuousAt.mpr fun x =>
      (oscillatoryFactor_hasDerivAt T x).continuousAt
  have hfcont : ContinuousOn f (uIcc a b) := HasDerivAt.continuousOn hf
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    he.continuousOn hfcont
    (fun x _ => oscillatoryFactor_hasDerivAt T x)
    (fun x hx => hf x (Ioo_subset_Icc_self hx))
    ((continuous_const.mul he).intervalIntegrable a b) hf'
  rw [hperiod, hphase, sub_self, zero_sub] at h
  have hfact : (∫ x in a..b, Complex.I * T * oscillatoryFactor T x * f x) =
      (Complex.I * T) * (∫ x in a..b, oscillatoryFactor T x * f x) := by
    simp_rw [mul_assoc, intervalIntegral.integral_const_mul]
  rw [hfact] at h
  simpa only [neg_mul] using h

/-- Two periodic derivatives bound the Fourier coefficient by `T⁻²`.
No asymptotic decay of the smooth term is assumed. -/
theorem smooth_periodic_fourier_bound_ne_zero
    {f₀ f₁ f₂ : ℝ → ℂ} {a b T C : ℝ} (hT : T ≠ 0)
    (h₁ : ∀ x ∈ uIcc a b, HasDerivAt f₀ (f₁ x) x)
    (h₂ : ∀ x ∈ uIcc a b, HasDerivAt f₁ (f₂ x) x)
    (hint₂ : IntervalIntegrable f₂ volume a b)
    (hp₀ : f₀ b = f₀ a) (hp₁ : f₁ b = f₁ a)
    (hphase : oscillatoryFactor T b = oscillatoryFactor T a)
    (hbound : ∀ x ∈ uIoc a b, ‖f₂ x‖ ≤ C) :
    ‖∫ x in a..b, oscillatoryFactor T x * f₀ x‖ ≤ C * |b - a| / T ^ 2 := by
  have hint₁ : IntervalIntegrable f₁ volume a b :=
    (HasDerivAt.continuousOn h₂).intervalIntegrable
  have hfirst := periodic_fourier_derivative h₁ hint₁ hp₀ hphase
  have hsecond := periodic_fourier_derivative h₂ hint₂ hp₁ hphase
  rw [hfirst] at hsecond
  have heq : ‖∫ x in a..b, oscillatoryFactor T x * f₂ x‖ =
      T ^ 2 * ‖∫ x in a..b, oscillatoryFactor T x * f₀ x‖ := by
    rw [hsecond, norm_mul, norm_mul]
    simp only [norm_neg, norm_mul, norm_I, one_mul, norm_real,
      Real.norm_eq_abs]
    rw [← mul_assoc, ← sq, sq_abs]
  have hnorm : ‖∫ x in a..b, oscillatoryFactor T x * f₂ x‖ ≤ C * |b - a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [norm_mul, oscillatoryFactor_norm, one_mul]
    exact hbound x hx
  rw [heq] at hnorm
  apply (le_div_iff₀ (sq_pos_of_ne_zero hT)).mpr
  simpa only [mul_comm] using hnorm

theorem smooth_periodic_fourier_bound
    {f₀ f₁ f₂ : ℝ → ℂ} {a b T C : ℝ} (hT : 0 < T)
    (h₁ : ∀ x ∈ uIcc a b, HasDerivAt f₀ (f₁ x) x)
    (h₂ : ∀ x ∈ uIcc a b, HasDerivAt f₁ (f₂ x) x)
    (hint₂ : IntervalIntegrable f₂ volume a b)
    (hp₀ : f₀ b = f₀ a) (hp₁ : f₁ b = f₁ a)
    (hphase : oscillatoryFactor T b = oscillatoryFactor T a)
    (hbound : ∀ x ∈ uIoc a b, ‖f₂ x‖ ≤ C) :
    ‖∫ x in a..b, oscillatoryFactor T x * f₀ x‖ ≤ C * |b - a| / T ^ 2 :=
  smooth_periodic_fourier_bound_ne_zero hT.ne' h₁ h₂ hint₂ hp₀ hp₁ hphase hbound

/-- A compactly supported twice differentiable amplitude has a quantitative
whole-line Fourier bound. Compact support supplies integrability of both
derivatives and both boundary limits. -/
theorem compact_support_fourier_bound (f₀ f₁ f₂ : ℝ → ℂ)
    (h₁ : ∀ u, HasDerivAt f₀ (f₁ u) u)
    (h₂ : ∀ u, HasDerivAt f₁ (f₂ u) u)
    (hc₂ : Continuous f₂) (hs : HasCompactSupport f₀)
    {T : ℝ} (hT : 0 < T) :
    ‖∫ u : ℝ, Complex.exp (I * (T : ℂ) * u) * f₀ u‖ ≤
      (∫ u : ℝ, ‖f₂ u‖) / T ^ 2 := by
  have hc₀ : Continuous f₀ := continuous_iff_continuousAt.mpr fun u => (h₁ u).continuousAt
  have hc₁ : Continuous f₁ := continuous_iff_continuousAt.mpr fun u => (h₂ u).continuousAt
  have he₁ : f₁ = deriv f₀ := funext fun u => (h₁ u).deriv.symm
  have he₂ : f₂ = deriv f₁ := funext fun u => (h₂ u).deriv.symm
  have hs₁ : HasCompactSupport f₁ := by rw [he₁]; exact hs.deriv
  have hs₂ : HasCompactSupport f₂ := by rw [he₂]; exact hs₁.deriv
  have hi₀ : Integrable f₀ := hc₀.integrable_of_hasCompactSupport hs
  have hi₁ : Integrable f₁ := hc₁.integrable_of_hasCompactSupport hs₁
  have hi₂ : Integrable f₂ := hc₂.integrable_of_hasCompactSupport hs₂
  have hz₀ : Filter.Tendsto f₀ (Bornology.cobounded ℝ) (nhds 0) :=
    Filter.Tendsto.congr' (compact_cutoff_eventually_zero f₀ hs).symm tendsto_const_nhds
  have hz₁ : Filter.Tendsto f₁ (Bornology.cobounded ℝ) (nhds 0) :=
    Filter.Tendsto.congr' (compact_cutoff_eventually_zero f₁ hs₁).symm tendsto_const_nhds
  have ht := tendsto_oscillatory_integral_second_derivative f₀ f₁ f₂
    h₁ h₂ hi₁ hi₂ hz₀ hz₁ hT.ne'
  have ht' := intervalIntegral_tendsto_integral (integrable_oscillatory_mul T hi₀)
    Filter.tendsto_neg_atTop_atBot Filter.tendsto_id
  rw [tendsto_nhds_unique ht' ht]
  simpa only [one_div, div_eq_inv_mul, mul_one] using norm_second_derivative_remainder f₂ hT

/-- Local derivative information on the topological support of a cutoff
suffices for a global product derivative. No behavior is required of the
uncut amplitude away from that support. -/
theorem hasDerivAt_cutoff_mul {χ f f' : ℝ → ℂ} {u : ℝ}
    (hχ : DifferentiableAt ℝ χ u)
    (hf : u ∈ tsupport χ → HasDerivAt f (f' u) u) :
    HasDerivAt (fun u => χ u * f u)
      (deriv χ u * f u + χ u * f' u) u := by
  by_cases hu : u ∈ tsupport χ
  · exact hχ.hasDerivAt.mul (hf hu)
  · have hχ₀ : χ u = 0 := image_eq_zero_of_notMem_tsupport hu
    have hdχ : deriv χ u = 0 := deriv_of_notMem_tsupport hu
    have heq : (fun u => χ u * f u) =ᶠ[nhds u] fun _ => (0 : ℂ) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hu] with x hx
      simp only [hx, zero_mul, Pi.zero_apply]
    simpa only [hχ₀, hdχ, zero_mul, add_zero] using
      (hasDerivAt_const u (0 : ℂ)).congr_of_eventuallyEq heq

end Maxwell.Green
