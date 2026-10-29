import Maxwell.Continuum.TransverseGaussian

/-! The damped complex exponential estimate used at a transverse pole.
Both the actual phase and its quadratic part have a positive imaginary
part; the connecting segment therefore has the same Gaussian damping. -/

noncomputable section

namespace Maxwell.Continuum.TransverseGaussian

open MeasureTheory

def wave (T : ℝ) (p : ℂ) : ℂ := Complex.exp (Complex.I * T * p)

def gaussian (T q : ℝ) : ℂ := (Real.exp (-T * q) : ℂ)

theorem wave_norm (T : ℝ) (p : ℂ) :
    ‖wave T p‖ = Real.exp (-T * p.im) := by
  simp [wave, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem gaussian_norm (T q : ℝ) :
    ‖gaussian T q‖ = Real.exp (-T * q) := by
  simp only [gaussian, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]

theorem wave_norm_le {T c : ℝ} (hT : 0 ≤ T) {p : ℂ} {r : ℝ}
    (hp : c * r ^ 2 ≤ p.im) :
    ‖wave T p‖ ≤ Real.exp (-(c * T) * r ^ 2) := by
  rw [wave_norm]
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_le_mul_of_nonneg_left hp hT]

theorem wave_sub_gaussian_le {T c M r q : ℝ} {p : ℂ}
    (hT : 0 ≤ T) (hp : c * r ^ 2 ≤ p.im) (hq : c * r ^ 2 ≤ q)
    (he : ‖p - Complex.I * q‖ ≤ M * r ^ 3) :
    ‖wave T p - gaussian T q‖ ≤
      (T * M * r ^ 3) * Real.exp (-(c * T) * r ^ 2) := by
  have hz : (Complex.I * (T : ℂ) * p).re ≤ -(c * T) * r ^ 2 := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, one_mul, mul_zero, sub_zero,
      zero_add, zero_sub]
    nlinarith only [mul_le_mul_of_nonneg_left hp hT]
  have hw : (-((T : ℂ) * q)).re ≤ -(c * T) * r ^ 2 := by
    simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    nlinarith only [mul_le_mul_of_nonneg_left hq hT]
  have hd : Complex.I * (T : ℂ) * p - -((T : ℂ) * q) =
      Complex.I * T * (p - Complex.I * q) := by
    calc
      _ = Complex.I * T * p + (T : ℂ) * q := by ring
      _ = _ := by ring_nf; simp only [Complex.I_sq, neg_mul, one_mul, sub_neg_eq_add]
  have hn : ‖Complex.I * (T : ℂ) * p - -((T : ℂ) * q)‖ =
      T * ‖p - Complex.I * q‖ := by
    rw [hd, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_of_nonneg hT, one_mul]
  have h := exp_sub_le hz hw
  rw [hn] at h
  change ‖wave T p - gaussian T q‖ ≤ _
  have hg : gaussian T q = Complex.exp (-((T : ℂ) * q)) := by
    simp only [gaussian, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]
    congr 1
    ring
  rw [wave, hg]
  calc
    _ ≤ Real.exp (-(c * T) * r ^ 2) * (T * ‖p - Complex.I * q‖) := h
    _ ≤ Real.exp (-(c * T) * r ^ 2) * (T * (M * r ^ 3)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hT) (Real.exp_pos _).le
    _ = _ := by ring

theorem amplitude_error_pointwise {T c L M r q : ℝ} {A A₀ p : ℂ}
    (hT : 0 ≤ T) (hL : 0 ≤ L) (hr : 0 ≤ r)
    (hp : c * r ^ 2 ≤ p.im) (hq : c * r ^ 2 ≤ q)
    (he : ‖p - Complex.I * q‖ ≤ M * r ^ 3)
    (hA : ‖A - A₀‖ ≤ L * r) :
    ‖A * wave T p - A₀ * gaussian T q‖ ≤
      L * (r * Real.exp (-(c * T) * r ^ 2)) +
        (‖A₀‖ * T * M) * (r ^ 3 * Real.exp (-(c * T) * r ^ 2)) := by
  have hid : A * wave T p - A₀ * gaussian T q =
      (A - A₀) * wave T p + A₀ * (wave T p - gaussian T q) := by ring
  rw [hid]
  calc
    _ ≤ ‖A - A₀‖ * ‖wave T p‖ + ‖A₀‖ * ‖wave T p - gaussian T q‖ :=
      (norm_add_le _ _).trans_eq (by rw [norm_mul, norm_mul])
    _ ≤ (L * r) * Real.exp (-(c * T) * r ^ 2) +
        ‖A₀‖ * ((T * M * r ^ 3) * Real.exp (-(c * T) * r ^ 2)) := by
      apply add_le_add
      · exact mul_le_mul hA (wave_norm_le hT hp) (norm_nonneg _) (mul_nonneg hL hr)
      · exact mul_le_mul_of_nonneg_left (wave_sub_gaussian_le hT hp hq he) (norm_nonneg _)
    _ = _ := by ring

end Maxwell.Continuum.TransverseGaussian
