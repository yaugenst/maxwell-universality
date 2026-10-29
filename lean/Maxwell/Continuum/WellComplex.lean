import Maxwell.Continuum.WellBump
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RealDeriv

/-! Explicit complex-line neighborhoods for the radial bump. -/

noncomputable section

namespace Maxwell.Continuum.Well

open Set Metric

/-- The reciprocal remains in the right half-plane on an explicit relative disc. -/
theorem inverse_re_lower (s : ℝ) (hs : 0 < s) (d : ℂ)
    (hd : ‖d - (s : ℂ)‖ ≤ s / 10) : 1 / (2 * s) ≤ d⁻¹.re := by
  have hre : |d.re - s| ≤ s / 10 := by
    have hre₀ : |d.re - s| ≤ ‖d - (s : ℂ)‖ := by
      simpa only [Complex.sub_re, Complex.ofReal_re] using
        Complex.abs_re_le_norm (d - (s : ℂ))
    exact hre₀.trans hd
  have hdl : 9 * s / 10 ≤ d.re := by linarith [(abs_le.mp hre).1]
  have hdn : ‖d‖ ≤ 11 * s / 10 := by
    have h := norm_add_le (d - (s : ℂ)) (s : ℂ)
    simp only [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs] at h
    linarith
  have hdz : d ≠ 0 := by
    intro hz
    simp only [hz, Complex.zero_re] at hdl
    linarith
  have hdq : Complex.normSq d ≤ (11 * s / 10) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    gcongr
  rw [Complex.inv_re]
  apply (div_le_div_iff₀ (by positivity) (Complex.normSq_pos.mpr hdz)).mpr
  nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hdl)]

def lineDenominator (s a b : ℝ) (z : ℂ) : ℂ :=
  (s : ℂ) - 2 * (a : ℂ) * z - (b : ℂ) * z ^ 2

theorem lineDenominator_close (s a b : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (z : ℂ) (hz : ‖z‖ ≤ s / 100) :
    ‖lineDenominator s a b z - (s : ℂ)‖ ≤ s / 10 := by
  have hz₁ : ‖z‖ ≤ 1 := by linarith
  have he : lineDenominator s a b z - (s : ℂ) =
      -(2 * (a : ℂ) * z + (b : ℂ) * z ^ 2) := by unfold lineDenominator; ring
  rw [he, norm_neg]
  calc
    ‖2 * (a : ℂ) * z + (b : ℂ) * z ^ 2‖ ≤
        ‖2 * (a : ℂ) * z‖ + ‖(b : ℂ) * z ^ 2‖ := norm_add_le _ _
    _ = 2 * |a| * ‖z‖ + |b| * ‖z‖ ^ 2 := by
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
      norm_num
    _ ≤ 2 * 1 * ‖z‖ + 1 * ‖z‖ ^ 2 := by gcongr
    _ = 2 * ‖z‖ + ‖z‖ ^ 2 := by ring
    _ ≤ 3 * ‖z‖ := by nlinarith [norm_nonneg z]
    _ ≤ s / 10 := by linarith

theorem lineDenominator_ne_zero (s a b : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1)
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (z : ℂ) (hz : ‖z‖ ≤ s / 100) :
    lineDenominator s a b z ≠ 0 := by
  have h := inverse_re_lower s hs _ (lineDenominator_close s a b hs hs₁ ha hb z hz)
  intro hzero
  simp only [hzero, inv_zero, Complex.zero_re] at h
  have : 0 < 1 / (2 * s) := by positivity
  linarith

def complexLineBump (c s a b : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(c : ℂ) / lineDenominator s a b z)

theorem complexLineBump_norm_le (c s a b : ℝ) (hc : 1 / 2 ≤ c)
    (hs : 0 < s) (hs₁ : s ≤ 1) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (z : ℂ) (hz : ‖z‖ ≤ s / 100) :
    ‖complexLineBump c s a b z‖ ≤ Real.exp (-1 / (4 * s)) := by
  have hinv := inverse_re_lower s hs _ (lineDenominator_close s a b hs hs₁ ha hb z hz)
  have hpos : 0 < 1 / (2 * s) := by positivity
  have hmul : (1 / 2 : ℝ) * (1 / (2 * s)) ≤ c * (lineDenominator s a b z)⁻¹.re := by
    exact mul_le_mul hc hinv hpos.le (by linarith)
  rw [complexLineBump, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [div_eq_mul_inv, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.neg_im, Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
  have he : (1 / 2 : ℝ) * (1 / (2 * s)) = 1 / (4 * s) := by ring
  rw [he] at hmul
  simpa only [div_eq_mul_inv, neg_mul, one_mul] using neg_le_neg hmul

theorem complexLineBump_diffContOnCl (c s a b : ℝ)
    (hs : 0 < s) (hs₁ : s ≤ 1) (ha : |a| ≤ 1) (hb : |b| ≤ 1) :
    DiffContOnCl ℂ (complexLineBump c s a b) (ball (0 : ℂ) (s / 100)) := by
  have hden : Differentiable ℂ (lineDenominator s a b) := by unfold lineDenominator; fun_prop
  have hf : DifferentiableOn ℂ (complexLineBump c s a b) (closedBall (0 : ℂ) (s / 100)) := by
    intro z hz
    exact ((differentiableAt_const (-(c : ℂ))).div hden.differentiableAt
      (lineDenominator_ne_zero s a b hs hs₁ ha hb z (by simpa using hz))).cexp.differentiableWithinAt
  exact ⟨hf.mono ball_subset_closedBall, by
    rw [closure_ball _ (ne_of_gt (by positivity : 0 < s / 100))]
    exact hf.continuousOn⟩

/-- Actual Cauchy estimate for the explicit analytic extension, with a symbolic radius. -/
theorem complexLineBump_cauchy (c s a b : ℝ) (hc : 1 / 2 ≤ c)
    (hs : 0 < s) (hs₁ : s ≤ 1) (ha : |a| ≤ 1) (hb : |b| ≤ 1) (K : ℕ) :
    ‖iteratedDeriv K (complexLineBump c s a b) 0‖ ≤
      K.factorial * Real.exp (-1 / (4 * s)) / (s / 100) ^ K := by
  apply Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le K (by positivity)
    (complexLineBump_diffContOnCl c s a b hs hs₁ ha hb)
  intro z hz
  exact complexLineBump_norm_le c s a b hc hs hs₁ ha hb z (by
    have := mem_sphere_zero_iff_norm.mp hz
    exact this.le)

theorem pow_mul_exp_neg_le_factorial (x : ℝ) (hx : 0 ≤ x) (K : ℕ) :
    x ^ K * Real.exp (-x) ≤ K.factorial := by
  have h := (div_le_iff₀ (show (0 : ℝ) < K.factorial by positivity)).mp
    (Real.pow_div_factorial_le_exp x hx K)
  calc
    x ^ K * Real.exp (-x) ≤ (Real.exp x * K.factorial) * Real.exp (-x) :=
      mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = K.factorial := by rw [Real.exp_neg]; field_simp

/-- Symbolic factorial majorant; no large constants are expanded. -/
theorem cauchy_majorant_le_gevrey (s : ℝ) (hs : 0 < s) (K : ℕ) :
    K.factorial * Real.exp (-1 / (4 * s)) / (s / 100) ^ K ≤
      (400 : ℝ) ^ K * (K.factorial : ℝ) ^ 2 := by
  have he : -1 / (4 * s) = -(1 / (4 * s)) := by ring
  have hr : 100 / s = 400 * (1 / (4 * s)) := by ring
  calc
    K.factorial * Real.exp (-1 / (4 * s)) / (s / 100) ^ K =
        (400 : ℝ) ^ K * K.factorial *
          ((1 / (4 * s)) ^ K * Real.exp (-(1 / (4 * s)))) := by
      rw [div_eq_mul_inv, ← inv_pow, inv_div, hr, mul_pow, he]
      ring
    _ ≤ (400 : ℝ) ^ K * K.factorial * K.factorial :=
      mul_le_mul_of_nonneg_left
        (pow_mul_exp_neg_le_factorial _ (by positivity) K) (by positivity)
    _ = (400 : ℝ) ^ K * (K.factorial : ℝ) ^ 2 := by ring

theorem complexLineBump_gevrey (c s a b : ℝ) (hc : 1 / 2 ≤ c)
    (hs : 0 < s) (hs₁ : s ≤ 1) (ha : |a| ≤ 1) (hb : |b| ≤ 1) (K : ℕ) :
    ‖iteratedDeriv K (complexLineBump c s a b) 0‖ ≤
      (400 : ℝ) ^ K * (K.factorial : ℝ) ^ 2 :=
  (complexLineBump_cauchy c s a b hc hs hs₁ ha hb K).trans
    (cauchy_majorant_le_gevrey s hs K)

end Maxwell.Continuum.Well
