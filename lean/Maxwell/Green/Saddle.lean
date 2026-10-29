import Maxwell.Green.Phase
import Maxwell.Green.Gaussian
import Maxwell.Green.Tail

/-! The localized transverse saddle integral, including its quantitative remainder.
The inputs are pointwise Taylor estimates and the ordinary cutoff conditions.
Integrability and the integral asymptotic are conclusions. -/

noncomputable section

namespace Maxwell.Green

open MeasureTheory Filter Real
open scoped Topology

/-- The quadratic pole location in an orthonormal eigenbasis of the
transverse Hessian. -/
def quadraticPhase (v q₁ q₂ : ℝ) (w : ℂ) : ℂ :=
  Complex.I * (((q₁ * w.re ^ 2 + q₂ * w.im ^ 2) / (2 * v) : ℝ) : ℂ)

theorem quadraticPhase_im (v q₁ q₂ : ℝ) (w : ℂ) :
    (quadraticPhase v q₁ q₂ w).im = (q₁ * w.re ^ 2 + q₂ * w.im ^ 2) / (2 * v) := by
  unfold quadraticPhase
  simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, one_mul, zero_add]

/-- Positive transverse eigenvalues provide the Gaussian lower bound. -/
theorem quadraticPhase_im_lower {v q₁ q₂ c : ℝ} (hv : 0 < v)
    (h₁ : 2 * v * c ≤ q₁) (h₂ : 2 * v * c ≤ q₂) (w : ℂ) :
    c * ‖w‖ ^ 2 ≤ (quadraticPhase v q₁ q₂ w).im := by
  rw [quadraticPhase_im]
  apply (le_div_iff₀ (by positivity : 0 < 2 * v)).mpr
  rw [Complex.sq_norm, Complex.normSq_apply]
  nlinarith [mul_le_mul_of_nonneg_right h₁ (sq_nonneg w.re),
    mul_le_mul_of_nonneg_right h₂ (sq_nonneg w.im)]

theorem exp_quadraticPhase (T v q₁ q₂ : ℝ) (w : ℂ) :
    Complex.exp (Complex.I * T * quadraticPhase v q₁ q₂ w) =
      (exp (-(T / (2 * v)) * (q₁ * w.re ^ 2 + q₂ * w.im ^ 2)) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  unfold quadraticPhase
  push_cast
  calc
    _ = -(T : ℂ) * (((q₁ : ℂ) * (w.re : ℂ) ^ 2 +
        (q₂ : ℂ) * (w.im : ℂ) ^ 2) / (2 * (v : ℂ))) := by
      calc
        _ = Complex.I ^ 2 * (T : ℂ) *
            (((q₁ : ℂ) * (w.re : ℂ) ^ 2 + (q₂ : ℂ) * (w.im : ℂ) ^ 2) /
              (2 * (v : ℂ))) := by ring
        _ = _ := by rw [Complex.I_sq]; ring
    _ = _ := by ring

/-- The model integral has the precise transverse determinant coefficient. -/
theorem integral_quadraticPhase {T v q₁ q₂ : ℝ}
    (hT : 0 < T) (hv : 0 < v) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) :
    (∫ w : ℂ, Complex.exp (Complex.I * T * quadraticPhase v q₁ q₂ w)) =
      ((2 * π * v / (T * sqrt (q₁ * q₂)) : ℝ) : ℂ) := by
  simp_rw [exp_quadraticPhase]
  rw [integral_complex_ofReal, transverse_gaussian_integral_complex_domain hT hv hq₁ hq₂]

/-- Local Taylor data in the two-dimensional transverse chart. The model phase
is later specialized to the positive quadratic term of the pole location. -/
structure LocalSaddleData where
  cutoff : ℂ → ℝ
  amplitude : ℂ → ℂ
  phase : ℂ → ℂ
  model : ℂ → ℂ
  amplitude0 : ℂ
  c : ℝ
  K₁ : ℝ
  K₃ : ℝ
  δ : ℝ
  c_pos : 0 < c
  K₁_nonneg : 0 ≤ K₁
  K₃_nonneg : 0 ≤ K₃
  δ_pos : 0 < δ
  cutoff_measurable : Measurable cutoff
  amplitude_measurable : Measurable amplitude
  phase_measurable : Measurable phase
  model_measurable : Measurable model
  cutoff_nonneg : ∀ w, 0 ≤ cutoff w
  cutoff_le_one : ∀ w, cutoff w ≤ 1
  cutoff_core : ∀ w, ‖w‖ < δ → cutoff w = 1
  model_im : ∀ w, c * ‖w‖ ^ 2 ≤ (model w).im
  phase_im : ∀ w, cutoff w ≠ 0 → c * ‖w‖ ^ 2 ≤ (phase w).im
  amplitude_error : ∀ w, cutoff w ≠ 0 → ‖amplitude w - amplitude0‖ ≤ K₁ * ‖w‖
  phase_error : ∀ w, cutoff w ≠ 0 → ‖phase w - model w‖ ≤ K₃ * ‖w‖ ^ 3

namespace LocalSaddleData

variable (D : LocalSaddleData)

def kernel (T : ℝ) (w : ℂ) : ℂ :=
  (D.cutoff w : ℂ) * (D.amplitude w * Complex.exp (Complex.I * T * D.phase w))

def modelKernel (T : ℝ) (w : ℂ) : ℂ :=
  D.amplitude0 * Complex.exp (Complex.I * T * D.model w)

def amplitudeError (T : ℝ) (w : ℂ) : ℂ :=
  (D.cutoff w : ℂ) *
    (D.amplitude w * Complex.exp (Complex.I * T * D.phase w) - D.modelKernel T w)

def cutoffError (T : ℝ) (w : ℂ) : ℂ :=
  ((D.cutoff w : ℂ) - 1) * D.modelKernel T w

def errorConstant : ℝ :=
  D.K₁ * π * D.c ^ (-(3 : ℝ) / 2) * Gamma ((3 : ℝ) / 2) +
  (‖D.amplitude0‖ * D.K₃) * π * D.c ^ (-(5 : ℝ) / 2) * Gamma ((5 : ℝ) / 2)

theorem amplitudeError_bound (T : ℝ) (hT : 0 ≤ T) (w : ℂ) :
    ‖D.amplitudeError T w‖ ≤
      D.K₁ * (‖w‖ * exp (-(D.c * T) * ‖w‖ ^ 2)) +
      ((‖D.amplitude0‖ * D.K₃) * T) *
        (‖w‖ ^ 3 * exp (-(D.c * T) * ‖w‖ ^ 2)) := by
  by_cases hw : D.cutoff w = 0
  · simp only [amplitudeError, hw, Complex.ofReal_zero, zero_mul, norm_zero]
    have := D.K₁_nonneg
    have := D.K₃_nonneg
    positivity
  · have h := amplitude_phase_error_bound hT (D.phase_im w hw) (D.model_im w)
      (D.amplitude_error w hw) (D.phase_error w hw)
    have hcut : ‖(D.cutoff w : ℂ)‖ ≤ 1 := by
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (D.cutoff_nonneg w)] using D.cutoff_le_one w
    calc
      ‖D.amplitudeError T w‖ ≤
          ‖D.amplitude w * Complex.exp (Complex.I * T * D.phase w) -
            D.amplitude0 * Complex.exp (Complex.I * T * D.model w)‖ := by
        dsimp [amplitudeError, modelKernel]
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) hcut
      _ ≤ _ := by
        have he : -T * D.c * ‖w‖ ^ 2 = -(D.c * T) * ‖w‖ ^ 2 := by ring
        rw [he] at h
        exact h.trans_eq (by ring)

theorem amplitudeError_integrable (T : ℝ) (hT : 0 < T) :
    Integrable (D.amplitudeError T) := by
  have hb := mul_pos D.c_pos hT
  apply (((first_gaussian_moment_integrable hb).const_mul D.K₁).add
    ((third_gaussian_moment_integrable hb).const_mul
      ((‖D.amplitude0‖ * D.K₃) * T))).mono'
  · apply Measurable.aestronglyMeasurable
    have := D.cutoff_measurable
    have := D.amplitude_measurable
    have := D.phase_measurable
    have := D.model_measurable
    unfold amplitudeError modelKernel
    fun_prop
  · exact Filter.Eventually.of_forall (D.amplitudeError_bound T hT.le)

theorem modelKernel_bound (T : ℝ) (hT : 0 ≤ T) (w : ℂ) :
    ‖D.modelKernel T w‖ ≤ ‖D.amplitude0‖ * exp (-(D.c * T) * ‖w‖ ^ 2) := by
  dsimp [modelKernel]
  rw [norm_mul, Complex.norm_exp]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (D.model_im w) hT
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_add, mul_zero,
    one_mul, sub_zero, zero_sub]
  nlinarith

theorem cutoffError_bound (T : ℝ) (hT : 0 ≤ T) (w : ℂ) :
    ‖D.cutoffError T w‖ ≤ ‖D.amplitude0‖ * exp (-(D.c * T) * ‖w‖ ^ 2) := by
  have hcut : ‖(D.cutoff w : ℂ) - 1‖ ≤ 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [D.cutoff_nonneg w], by linarith [D.cutoff_le_one w]⟩
  calc
    ‖D.cutoffError T w‖ ≤ ‖D.modelKernel T w‖ := by
      dsimp [cutoffError]
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hcut
    _ ≤ _ := D.modelKernel_bound T hT w

theorem cutoffError_zero (T : ℝ) (w : ℂ) (hw : ‖w‖ < D.δ) :
    D.cutoffError T w = 0 := by
  simp [cutoffError, D.cutoff_core w hw]

theorem cutoffError_integrable (T : ℝ) (hT : 0 < T) :
    Integrable (D.cutoffError T) := by
  apply integrable_cutoff_tail _ ‖D.amplitude0‖ (D.c * T) D.δ _
    (norm_nonneg _) (mul_pos D.c_pos hT) D.δ_pos.le
    (D.cutoffError_zero T) (D.cutoffError_bound T hT.le)
  apply Measurable.aestronglyMeasurable
  have := D.cutoff_measurable
  have := D.model_measurable
  unfold cutoffError modelKernel
  fun_prop

theorem modelKernel_integrable (T : ℝ) (hT : 0 < T) :
    Integrable (D.modelKernel T) := by
  apply ((integrable_radial_gaussian (D.c * T) (mul_pos D.c_pos hT)).const_mul
    ‖D.amplitude0‖).mono'
  · apply Measurable.aestronglyMeasurable
    have := D.model_measurable
    unfold modelKernel
    fun_prop
  · exact Filter.Eventually.of_forall (D.modelKernel_bound T hT.le)

theorem kernel_decomposition (T : ℝ) (w : ℂ) :
    D.kernel T w = D.amplitudeError T w + D.cutoffError T w + D.modelKernel T w := by
  dsimp [kernel, amplitudeError, cutoffError, modelKernel]
  ring

theorem kernel_integrable (T : ℝ) (hT : 0 < T) : Integrable (D.kernel T) := by
  have h := ((D.amplitudeError_integrable T hT).add
    (D.cutoffError_integrable T hT)).add (D.modelKernel_integrable T hT)
  exact h.congr (Filter.Eventually.of_forall fun w => (D.kernel_decomposition T w).symm)

/-- The complete quantitative saddle estimate: the local Taylor errors have
scale `T^(-3/2)`, while removing the Gaussian cutoff is exponentially small. -/
theorem integral_error_bound (T : ℝ) (hT : 0 < T) :
    ‖(∫ w, D.kernel T w) - ∫ w, D.modelKernel T w‖ ≤
      D.errorConstant * T ^ (-(3 : ℝ) / 2) +
        (2 * π * ‖D.amplitude0‖ / (D.c * T)) * exp (-(D.c * T) * D.δ ^ 2 / 2) := by
  have h₁ := gaussian_error_integral_bound hT D.c_pos (D.amplitudeError_bound T hT.le)
  have h₂ := norm_integral_scaled_cutoff_tail (D.cutoffError T)
    ‖D.amplitude0‖ D.c T D.δ (norm_nonneg _) D.c_pos hT D.δ_pos.le
    (D.cutoffError_zero T) (D.cutoffError_bound T hT.le)
  have heq : (∫ w, D.kernel T w) - ∫ w, D.modelKernel T w =
      (∫ w, D.amplitudeError T w) + ∫ w, D.cutoffError T w := by
    simp_rw [D.kernel_decomposition T]
    have hI12 : Integrable (fun w => D.amplitudeError T w + D.cutoffError T w) :=
      (D.amplitudeError_integrable T hT).add (D.cutoffError_integrable T hT)
    rw [integral_add hI12 (D.modelKernel_integrable T hT),
      integral_add (D.amplitudeError_integrable T hT) (D.cutoffError_integrable T hT)]
    ring
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add h₁ h₂)

/-- The claimed inverse-three-halves remainder follows with one threshold
for the whole family of transverse saddle integrals. -/
theorem eventually_integral_error_bound :
    ∀ᶠ T : ℝ in atTop,
      ‖(∫ w, D.kernel T w) - ∫ w, D.modelKernel T w‖ ≤
        (D.errorConstant + 1) * T ^ (-(3 : ℝ) / 2) := by
  filter_upwards [eventually_scaled_cutoff_tail_bound ‖D.amplitude0‖ D.c D.δ
    D.c_pos D.δ_pos, eventually_gt_atTop (0 : ℝ)] with T ht hT
  have hpow : 1 / T ^ ((3 : ℝ) / 2) = T ^ (-(3 : ℝ) / 2) := by
    rw [one_div, ← Real.rpow_neg hT.le]
    congr 1
    ring
  have h := (D.integral_error_bound T hT).trans
    (add_le_add_right ht (D.errorConstant * T ^ (-(3 : ℝ) / 2)))
  rw [hpow] at h
  exact h.trans_eq (by ring)

end LocalSaddleData

/-- Equation (21): local Taylor estimates imply the actual transverse saddle
integral coefficient, with an inverse-three-halves error for all large scales. -/
theorem localized_transverse_saddle (D : LocalSaddleData) {v q₁ q₂ : ℝ}
    (hv : 0 < v) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hmodel : D.model = quadraticPhase v q₁ q₂) :
    ∀ᶠ T : ℝ in atTop,
      ‖(∫ w, D.kernel T w) - D.amplitude0 *
          ((2 * π * v / (T * sqrt (q₁ * q₂)) : ℝ) : ℂ)‖ ≤
        (D.errorConstant + 1) * T ^ (-(3 : ℝ) / 2) := by
  filter_upwards [D.eventually_integral_error_bound, eventually_gt_atTop (0 : ℝ)] with T ht hT
  have hI : (∫ w, D.modelKernel T w) = D.amplitude0 *
      ((2 * π * v / (T * sqrt (q₁ * q₂)) : ℝ) : ℂ) := by
    unfold LocalSaddleData.modelKernel
    rw [hmodel, integral_const_mul, integral_quadraticPhase hT hv hq₁ hq₂]
  rwa [hI] at ht

end Maxwell.Green
