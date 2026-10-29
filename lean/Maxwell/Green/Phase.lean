import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Tactic

/-! # Quantitative error estimates in the transverse saddle calculation -/

open MeasureTheory Real Set

namespace Maxwell.Green

/-- Exponentiation is Lipschitz on a left half-plane, with the sharp bound
coming from the maximum real part along the joining segment. -/
theorem norm_exp_sub_le_of_re_le {z z₀ : ℂ} {a : ℝ}
    (hz : z.re ≤ a) (hz₀ : z₀.re ≤ a) :
    ‖Complex.exp z - Complex.exp z₀‖ ≤ ‖z - z₀‖ * exp a := by
  have hconv : Convex ℝ {w : ℂ | w.re ≤ a} := by
    intro x hx y hy u v hu hv huv
    change x.re ≤ a at hx
    change y.re ≤ a at hy
    change (u • x + v • y).re ≤ a
    simp only [Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    calc
      u * x.re + v * y.re ≤ u * a + v * a :=
        add_le_add (mul_le_mul_of_nonneg_left hx hu) (mul_le_mul_of_nonneg_left hy hv)
      _ = (u + v) * a := by ring
      _ = a := by rw [huv, one_mul]
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := Complex.exp) (f' := Complex.exp)
    (fun w _ => (Complex.hasDerivAt_exp w).hasDerivWithinAt)
    (fun w (hw : w.re ≤ a) => by rw [Complex.norm_exp]; exact exp_le_exp.mpr hw)
    hconv hz₀ hz
  simpa only [mul_comm] using h

/-- The cubic phase error retains the Gaussian decay factor. -/
theorem phase_error_bound {p p₀ : ℂ} {T c ρ K : ℝ}
    (hT : 0 ≤ T) (hp : c * ρ ^ 2 ≤ p.im)
    (hp₀ : c * ρ ^ 2 ≤ p₀.im) (herr : ‖p - p₀‖ ≤ K * ρ ^ 3) :
    ‖Complex.exp (Complex.I * T * p) - Complex.exp (Complex.I * T * p₀)‖ ≤
      T * K * ρ ^ 3 * exp (-T * c * ρ ^ 2) := by
  have hre (z : ℂ) : (Complex.I * (T : ℂ) * z).re = -T * z.im := by
    simp [Complex.mul_re, Complex.mul_im]
  have hz : (Complex.I * (T : ℂ) * p).re ≤ -T * c * ρ ^ 2 := by
    rw [hre]
    nlinarith [mul_le_mul_of_nonneg_left hp hT]
  have hz₀ : (Complex.I * (T : ℂ) * p₀).re ≤ -T * c * ρ ^ 2 := by
    rw [hre]
    nlinarith [mul_le_mul_of_nonneg_left hp₀ hT]
  have h := norm_exp_sub_le_of_re_le hz hz₀
  have hnorm : ‖Complex.I * (T : ℂ) * p - Complex.I * (T : ℂ) * p₀‖ =
      T * ‖p - p₀‖ := by
    rw [← mul_sub, norm_mul, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT]
  rw [hnorm] at h
  calc
    _ ≤ T * ‖p - p₀‖ * exp (-T * c * ρ ^ 2) := h
    _ ≤ T * (K * ρ ^ 3) * exp (-T * c * ρ ^ 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left herr hT) (exp_pos _).le
    _ = _ := by ring

/-- Linear amplitude variation and cubic phase variation give the two
Gaussian-weighted error terms integrated below. -/
theorem amplitude_phase_error_bound {a a₀ p p₀ : ℂ} {T c ρ K₁ K₃ : ℝ}
    (hT : 0 ≤ T) (hp : c * ρ ^ 2 ≤ p.im)
    (hp₀ : c * ρ ^ 2 ≤ p₀.im)
    (ha : ‖a - a₀‖ ≤ K₁ * ρ) (hphase : ‖p - p₀‖ ≤ K₃ * ρ ^ 3) :
    ‖a * Complex.exp (Complex.I * T * p) -
        a₀ * Complex.exp (Complex.I * T * p₀)‖ ≤
      K₁ * ρ * exp (-T * c * ρ ^ 2) +
        ‖a₀‖ * (T * K₃ * ρ ^ 3 * exp (-T * c * ρ ^ 2)) := by
  have hexp : ‖Complex.exp (Complex.I * T * p)‖ ≤ exp (-T * c * ρ ^ 2) := by
    rw [Complex.norm_exp]
    apply exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_add, mul_zero,
      one_mul, sub_zero, zero_sub]
    nlinarith [mul_le_mul_of_nonneg_left hp hT]
  calc
    _ = ‖(a - a₀) * Complex.exp (Complex.I * T * p) +
        a₀ * (Complex.exp (Complex.I * T * p) -
          Complex.exp (Complex.I * T * p₀))‖ := by congr 1; ring
    _ ≤ ‖(a - a₀) * Complex.exp (Complex.I * T * p)‖ +
        ‖a₀ * (Complex.exp (Complex.I * T * p) -
          Complex.exp (Complex.I * T * p₀))‖ := norm_add_le _ _
    _ = ‖a - a₀‖ * ‖Complex.exp (Complex.I * T * p)‖ +
        ‖a₀‖ * ‖Complex.exp (Complex.I * T * p) -
          Complex.exp (Complex.I * T * p₀)‖ := by rw [norm_mul, norm_mul]
    _ ≤ _ := add_le_add
      (mul_le_mul ha hexp (norm_nonneg _) ((norm_nonneg _).trans ha))
      (mul_le_mul_of_nonneg_left (phase_error_bound hT hp hp₀ hphase) (norm_nonneg _))

/-- The first transverse Gaussian moment, responsible for amplitude error. -/
theorem first_gaussian_moment {b : ℝ} (hb : 0 < b) :
    (∫ w : ℂ, ‖w‖ * exp (-b * ‖w‖ ^ 2)) =
      π * b ^ (-(3 : ℝ) / 2) * Gamma ((3 : ℝ) / 2) := by
  convert Complex.integral_rpow_mul_exp_neg_mul_rpow
    (p := 2) (q := 1) (by norm_num) (by norm_num) hb using 1 <;> norm_num

/-- The third transverse Gaussian moment, responsible for phase error. -/
theorem third_gaussian_moment {b : ℝ} (hb : 0 < b) :
    (∫ w : ℂ, ‖w‖ ^ 3 * exp (-b * ‖w‖ ^ 2)) =
      π * b ^ (-(5 : ℝ) / 2) * Gamma ((5 : ℝ) / 2) := by
  convert Complex.integral_rpow_mul_exp_neg_mul_rpow
    (p := 2) (q := 3) (by norm_num) (by norm_num) hb using 1 <;> norm_num

theorem first_gaussian_moment_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun w : ℂ => ‖w‖ * exp (-b * ‖w‖ ^ 2)) := by
  by_contra hi
  have hz := integral_undef hi
  rw [first_gaussian_moment hb] at hz
  have hp : 0 < π * b ^ (-(3 : ℝ) / 2) * Gamma ((3 : ℝ) / 2) := by positivity
  exact hp.ne' hz

theorem third_gaussian_moment_integrable {b : ℝ} (hb : 0 < b) :
    Integrable (fun w : ℂ => ‖w‖ ^ 3 * exp (-b * ‖w‖ ^ 2)) := by
  by_contra hi
  have hz := integral_undef hi
  rw [third_gaussian_moment hb] at hz
  have hp : 0 < π * b ^ (-(5 : ℝ) / 2) * Gamma ((5 : ℝ) / 2) := by positivity
  exact hp.ne' hz

/-- An amplitude error linear in transverse distance and a phase error cubic
in that distance together have the required `T^(-3/2)` integral bound. -/
theorem gaussian_error_integral_bound {E : ℂ → ℂ} {T c C₁ C₃ : ℝ}
    (hT : 0 < T) (hc : 0 < c)
    (hE : ∀ w, ‖E w‖ ≤
      C₁ * (‖w‖ * exp (-(c * T) * ‖w‖ ^ 2)) +
      (C₃ * T) * (‖w‖ ^ 3 * exp (-(c * T) * ‖w‖ ^ 2))) :
    ‖∫ w, E w‖ ≤
      (C₁ * π * c ^ (-(3 : ℝ) / 2) * Gamma ((3 : ℝ) / 2) +
       C₃ * π * c ^ (-(5 : ℝ) / 2) * Gamma ((5 : ℝ) / 2)) *
      T ^ (-(3 : ℝ) / 2) := by
  have hb := mul_pos hc hT
  have hI₁ := (first_gaussian_moment_integrable hb).const_mul C₁
  have hI₃ := (third_gaussian_moment_integrable hb).const_mul (C₃ * T)
  have hbound := norm_integral_le_of_norm_le (hI₁.add hI₃)
    (Filter.Eventually.of_forall hE)
  dsimp only [Pi.add_apply] at hbound
  rw [integral_add hI₁ hI₃, integral_const_mul, integral_const_mul,
    first_gaussian_moment hb, third_gaussian_moment hb,
    mul_rpow hc.le hT.le, mul_rpow hc.le hT.le] at hbound
  have hpower : T * T ^ (-(5 : ℝ) / 2) = T ^ (-(3 : ℝ) / 2) := by
    conv_lhs => lhs; rw [← rpow_one T]
    rw [← rpow_add hT]
    norm_num
  refine hbound.trans_eq ?_
  calc
    _ = C₁ * π * c ^ (-(3 : ℝ) / 2) * Gamma ((3 : ℝ) / 2) *
          T ^ (-(3 : ℝ) / 2) +
        C₃ * π * c ^ (-(5 : ℝ) / 2) * Gamma ((5 : ℝ) / 2) *
          (T * T ^ (-(5 : ℝ) / 2)) := by ring
    _ = _ := by rw [hpower]; ring

end Maxwell.Green
