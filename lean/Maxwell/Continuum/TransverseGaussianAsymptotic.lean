import Maxwell.Continuum.TransverseGaussianPhase
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! A quantitative transverse Gaussian approximation. The hypotheses are
local Taylor and damping bounds, not an asymptotic integral estimate. The
conclusion includes the part of the Gaussian outside the local pole chart. -/

noncomputable section

namespace Maxwell.Continuum.TransverseGaussian

open MeasureTheory Set Metric

structure LocalData where
  domain : Set Plane
  domain_measurable : MeasurableSet domain
  radius : ℝ
  radius_pos : 0 < radius
  ball_subset : ball 0 radius ⊆ domain
  amplitude : Plane → ℂ
  phase : Plane → ℂ
  quadratic : Plane → ℝ
  amplitude_measurable : Measurable amplitude
  phase_measurable : Measurable phase
  quadratic_measurable : Measurable quadratic
  center : ℂ
  damping : ℝ
  damping_pos : 0 < damping
  lipschitz : ℝ
  lipschitz_nonneg : 0 ≤ lipschitz
  cubic : ℝ
  cubic_nonneg : 0 ≤ cubic
  amplitude_error : ∀ x ∈ domain, ‖amplitude x - center‖ ≤ lipschitz * ‖x‖
  phase_error : ∀ x ∈ domain,
    ‖phase x - Complex.I * quadratic x‖ ≤ cubic * ‖x‖ ^ 3
  phase_damping : ∀ x ∈ domain, damping * ‖x‖ ^ 2 ≤ (phase x).im
  quadratic_damping : ∀ x, damping * ‖x‖ ^ 2 ≤ quadratic x

namespace LocalData

variable (D : LocalData)

def errorMajorant (T : ℝ) (x : Plane) : ℝ :=
  D.lipschitz * (‖x‖ * Real.exp (-(D.damping * T) * ‖x‖ ^ 2)) +
    (‖D.center‖ * T * D.cubic) *
      (‖x‖ ^ 3 * Real.exp (-(D.damping * T) * ‖x‖ ^ 2))

theorem errorMajorant_nonneg {T : ℝ} (hT : 0 ≤ T) (x : Plane) :
    0 ≤ D.errorMajorant T x := by
  unfold errorMajorant
  exact add_nonneg (mul_nonneg D.lipschitz_nonneg (by positivity))
    (mul_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) hT) D.cubic_nonneg) (by positivity))

theorem errorMajorant_integrable {T : ℝ} (hT : 0 < T) :
    Integrable (D.errorMajorant T) :=
  ((first_moment_integrable (mul_pos D.damping_pos hT)).const_mul _).add
    ((third_moment_integrable (mul_pos D.damping_pos hT)).const_mul _)

theorem pointwise_error {T : ℝ} (hT : 0 ≤ T) {x : Plane} (hx : x ∈ D.domain) :
    ‖D.amplitude x * wave T (D.phase x) - D.center * gaussian T (D.quadratic x)‖ ≤
      D.errorMajorant T x :=
  amplitude_error_pointwise hT D.lipschitz_nonneg (norm_nonneg x)
    (D.phase_damping x hx) (D.quadratic_damping x)
    (D.phase_error x hx) (D.amplitude_error x hx)

theorem quadratic_gaussian_integrable {T : ℝ} (hT : 0 < T) :
    Integrable (fun x => gaussian T (D.quadratic x)) := by
  apply (gaussian_integrable (mul_pos D.damping_pos hT)).mono'
    (by unfold gaussian; exact (D.quadratic_measurable.const_mul (-T)).exp.complex_ofReal.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x => by
    rw [gaussian_norm]
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_left (D.quadratic_damping x) hT.le]

theorem difference_integrableOn {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun x => D.amplitude x * wave T (D.phase x) -
      D.center * gaussian T (D.quadratic x)) D.domain := by
  apply (D.errorMajorant_integrable hT).integrableOn.mono' ?_ ?_
  · apply Measurable.aestronglyMeasurable
    unfold wave gaussian
    exact (D.amplitude_measurable.mul
      ((measurable_const.mul measurable_const).mul D.phase_measurable).cexp).sub
        (measurable_const.mul ((D.quadratic_measurable.const_mul (-T)).exp.complex_ofReal))
  · filter_upwards [ae_restrict_mem D.domain_measurable] with x hx
    exact D.pointwise_error hT.le hx

theorem integrand_integrableOn {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun x => D.amplitude x * wave T (D.phase x)) D.domain := by
  have h := (D.difference_integrableOn hT).add
    ((D.quadratic_gaussian_integrable hT).const_mul D.center).integrableOn
  exact h.congr (Filter.Eventually.of_forall fun x => sub_add_cancel _ _)

theorem local_error_le {T : ℝ} (hT : 0 < T) :
    ‖(∫ x in D.domain, D.amplitude x * wave T (D.phase x)) -
      D.center * ∫ x in D.domain, gaussian T (D.quadratic x)‖ ≤
        D.lipschitz * (2 * Real.pi / (D.damping * T * Real.sqrt (D.damping * T))) +
          (‖D.center‖ * T * D.cubic) *
            (32 * Real.pi / ((D.damping * T) ^ 2 * Real.sqrt (D.damping * T))) := by
  rw [← integral_const_mul, ← integral_sub (D.integrand_integrableOn hT)
    ((D.quadratic_gaussian_integrable hT).const_mul D.center).integrableOn]
  calc
    _ ≤ ∫ x in D.domain, D.errorMajorant T x := by
      apply norm_integral_le_of_norm_le (D.errorMajorant_integrable hT).integrableOn
      filter_upwards [ae_restrict_mem D.domain_measurable] with x hx
      exact D.pointwise_error hT.le hx
    _ ≤ ∫ x, D.errorMajorant T x :=
      setIntegral_le_integral (D.errorMajorant_integrable hT)
        (Filter.Eventually.of_forall (D.errorMajorant_nonneg hT.le))
    _ ≤ _ := by
      change (∫ x : Plane, D.lipschitz * (‖x‖ * Real.exp (-(D.damping * T) * ‖x‖ ^ 2)) +
        (‖D.center‖ * T * D.cubic) *
          (‖x‖ ^ 3 * Real.exp (-(D.damping * T) * ‖x‖ ^ 2))) ≤ _
      rw [integral_add
        ((first_moment_integrable (mul_pos D.damping_pos hT)).const_mul _)
        ((third_moment_integrable (mul_pos D.damping_pos hT)).const_mul _),
        integral_const_mul, integral_const_mul]
      exact add_le_add
        (mul_le_mul_of_nonneg_left (first_moment_integral (mul_pos D.damping_pos hT))
          D.lipschitz_nonneg)
        (mul_le_mul_of_nonneg_left (third_moment_integral (mul_pos D.damping_pos hT))
          (mul_nonneg (mul_nonneg (norm_nonneg _) hT.le) D.cubic_nonneg))

theorem gaussian_tail_le {T : ℝ} (hT : 0 < T) :
    ‖∫ x in D.domainᶜ, gaussian T (D.quadratic x)‖ ≤
      D.radius⁻¹ * (2 * Real.pi / (D.damping * T * Real.sqrt (D.damping * T))) := by
  have hi := (first_moment_integrable (mul_pos D.damping_pos hT)).const_mul D.radius⁻¹
  calc
    _ ≤ ∫ x in D.domainᶜ, D.radius⁻¹ *
        (‖x‖ * Real.exp (-(D.damping * T) * ‖x‖ ^ 2)) := by
      apply norm_integral_le_of_norm_le hi.integrableOn
      filter_upwards [ae_restrict_mem D.domain_measurable.compl] with x hx
      have hr : D.radius ≤ ‖x‖ := by
        by_contra! hr
        exact hx (D.ball_subset (by simpa only [mem_ball, dist_zero_right] using hr))
      have hm : 1 ≤ D.radius⁻¹ * ‖x‖ := by
        calc
          1 = D.radius⁻¹ * D.radius := (inv_mul_cancel₀ D.radius_pos.ne').symm
          _ ≤ _ := mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr D.radius_pos.le)
      rw [gaussian_norm]
      calc
        Real.exp (-T * D.quadratic x) ≤ Real.exp (-(D.damping * T) * ‖x‖ ^ 2) := by
          apply Real.exp_le_exp.mpr
          nlinarith only [mul_le_mul_of_nonneg_left (D.quadratic_damping x) hT.le]
        _ ≤ _ := by
          simpa only [one_mul, mul_assoc] using
            mul_le_mul_of_nonneg_right hm (Real.exp_pos (-(D.damping * T) * ‖x‖ ^ 2)).le
    _ ≤ ∫ x, D.radius⁻¹ * (‖x‖ * Real.exp (-(D.damping * T) * ‖x‖ ^ 2)) :=
      setIntegral_le_integral hi (Filter.Eventually.of_forall fun x => by
        exact mul_nonneg (inv_nonneg.mpr D.radius_pos.le) (by positivity))
    _ ≤ _ := by
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (first_moment_integral (mul_pos D.damping_pos hT))
        (inv_nonneg.mpr D.radius_pos.le)

def errorConstant : ℝ :=
  (D.lipschitz + ‖D.center‖ / D.radius) *
      (2 * Real.pi / (D.damping * Real.sqrt D.damping)) +
    (‖D.center‖ * D.cubic) * (32 * Real.pi / (D.damping ^ 2 * Real.sqrt D.damping))

/-- Explicit `T^(-3/2)` error, including the Gaussian tail beyond the pole chart. -/
theorem integral_error {T : ℝ} (hT : 0 < T) :
    ‖(∫ x in D.domain, D.amplitude x * wave T (D.phase x)) -
      D.center * ∫ x, gaussian T (D.quadratic x)‖ ≤
        D.errorConstant / (T * Real.sqrt T) := by
  have hid :
      (∫ x in D.domain, D.amplitude x * wave T (D.phase x)) -
          D.center * ∫ x, gaussian T (D.quadratic x) =
        ((∫ x in D.domain, D.amplitude x * wave T (D.phase x)) -
          D.center * ∫ x in D.domain, gaussian T (D.quadratic x)) -
          D.center * ∫ x in D.domainᶜ, gaussian T (D.quadratic x) := by
    rw [← integral_add_compl D.domain_measurable (D.quadratic_gaussian_integrable hT)]
    ring
  rw [hid]
  calc
    _ ≤ ‖(∫ x in D.domain, D.amplitude x * wave T (D.phase x)) -
          D.center * ∫ x in D.domain, gaussian T (D.quadratic x)‖ +
        ‖D.center‖ * ‖∫ x in D.domainᶜ, gaussian T (D.quadratic x)‖ := by
      simpa only [norm_mul] using norm_sub_le
        ((∫ x in D.domain, D.amplitude x * wave T (D.phase x)) -
          D.center * ∫ x in D.domain, gaussian T (D.quadratic x))
        (D.center * ∫ x in D.domainᶜ, gaussian T (D.quadratic x))
    _ ≤ (D.lipschitz * (2 * Real.pi / (D.damping * T * Real.sqrt (D.damping * T))) +
          (‖D.center‖ * T * D.cubic) *
            (32 * Real.pi / ((D.damping * T) ^ 2 * Real.sqrt (D.damping * T)))) +
        ‖D.center‖ * (D.radius⁻¹ *
          (2 * Real.pi / (D.damping * T * Real.sqrt (D.damping * T)))) :=
      add_le_add (D.local_error_le hT)
        (mul_le_mul_of_nonneg_left (D.gaussian_tail_le hT) (norm_nonneg _))
    _ = _ := by
      rw [Real.sqrt_mul D.damping_pos.le]
      unfold errorConstant
      field_simp [D.damping_pos.ne', hT.ne', (Real.sqrt_pos.mpr D.damping_pos).ne',
        (Real.sqrt_pos.mpr hT).ne', D.radius_pos.ne']
      ring

end LocalData

end Maxwell.Continuum.TransverseGaussian
