import Maxwell.Certificate.FourierBinding
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Maxwell.Spectral.BoxSymbols

open Maxwell.Certificate.FourierBinding Maxwell.Spectral.PeriodicYee
open MeasureTheory Set Filter
noncomputable section

/-- The imaginary-axis exponential has a global quadratic Taylor remainder
with coefficient one half, obtained by integrating its unit-modulus derivative. -/
theorem exp_imaginary_linear_remainder (x : ℝ) :
    ‖Complex.exp (Complex.I * (x : ℂ)) - 1 - Complex.I * (x : ℂ)‖ ≤ x^2/2 := by
  let f : ℝ → ℂ := fun t => Complex.exp (Complex.I * x * t) - 1 - Complex.I * x * t
  let g : ℝ → ℂ := fun t => (Complex.I * x) * (Complex.exp (Complex.I * x * t) - 1)
  have hd (t : ℝ) : HasDerivAt f (g t) t := by
    have he := (((hasDerivAt_id (t : ℂ)).const_mul (Complex.I * x)).cexp).comp_ofReal
    have hl := ((hasDerivAt_id (t : ℂ)).const_mul (Complex.I * x)).comp_ofReal
    convert (he.sub_const 1).sub hl using 1 <;> dsimp [f, g] <;> first | rfl | ring
  have hgc : Continuous g := by dsimp [g]; fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun t _ => hd t) (hgc.intervalIntegrable 0 1)
  have hnorm (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) : ‖g t‖ ≤ x^2*t := by
    have he : ‖Complex.exp (Complex.I * x * t) - 1‖ ≤ |x*t| := by
      simpa only [Complex.ofReal_mul, mul_assoc, Real.norm_eq_abs] using
        (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x*t))
    have h := mul_le_mul_of_nonneg_left he (abs_nonneg x)
    have hx : |x| * |x*t| = x^2*t := by
      rw [abs_mul, abs_of_pos ht.1]
      rw [← mul_assoc, ← sq, sq_abs]
    simpa only [g, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, one_mul, hx] using h
  have hb : IntervalIntegrable (fun t : ℝ => x^2*t) volume 0 1 :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 1
  have hn := intervalIntegral.norm_integral_le_of_norm_le (by norm_num : (0 : ℝ) ≤ 1)
    (Eventually.of_forall fun t ht => hnorm t ht) hb
  rw [hftc] at hn
  have hi : ∫ t : ℝ in 0..1, x^2*t = x^2/2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    norm_num
    ring
  rw [hi] at hn
  simpa [f] using hn

def phaseScale : ℝ := 2 * Real.pi / 20

theorem phaseScale_pos : 0 < phaseScale := by unfold phaseScale; positivity

theorem shiftSymbol_increment (c q : Momentum) (f : Frequency) (j : Direction) :
    shiftSymbol (c+q) f j = shiftSymbol c f j * Complex.exp (Complex.I * ((phaseScale*q j : ℝ) : ℂ)) := by
  unfold shiftSymbol phaseScale
  rw [← Complex.exp_add]
  congr 1
  simp only [Pi.add_apply]
  push_cast
  ring

theorem shiftSymbol_norm (c : Momentum) (f : Frequency) (j : Direction) :
    ‖shiftSymbol c f j‖ = 1 := by
  unfold shiftSymbol
  convert Complex.norm_exp_I_mul_ofReal
    (2*Real.pi/20*((reciprocalIndex f j : ℝ)+c j)) using 1
  push_cast
  rfl

def linearSymbol (c q : Momentum) (f : Frequency) (j : Direction) : ℂ :=
  shiftSymbol c f j * (Complex.I * ((phaseScale*q j : ℝ) : ℂ))

theorem symbol_increment_bound (c q : Momentum) (f : Frequency) (j : Direction) :
    ‖symbol (c+q) f j - symbol c f j‖ ≤ phaseScale * |q j| := by
  have hid : symbol (c+q) f j - symbol c f j =
      shiftSymbol c f j * (Complex.exp (Complex.I * ((phaseScale*q j : ℝ) : ℂ))-1) := by
    rw [symbol, symbol, shiftSymbol_increment]
    ring
  rw [hid, norm_mul, shiftSymbol_norm, one_mul]
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := phaseScale*q j)
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos phaseScale_pos] using h

theorem symbol_linear_remainder_bound (c q : Momentum) (f : Frequency) (j : Direction) :
    ‖symbol (c+q) f j - symbol c f j - linearSymbol c q f j‖ ≤
      phaseScale^2 * (q j)^2 / 2 := by
  have hid : symbol (c+q) f j - symbol c f j - linearSymbol c q f j =
      shiftSymbol c f j * (Complex.exp (Complex.I * ((phaseScale*q j : ℝ) : ℂ)) -
        1 - Complex.I * ((phaseScale*q j : ℝ) : ℂ)) := by
    rw [symbol, symbol, linearSymbol, shiftSymbol_increment]
    ring
  rw [hid, norm_mul, shiftSymbol_norm, one_mul]
  simpa only [mul_pow] using exp_imaginary_linear_remainder (phaseScale*q j)

def momentumNorm (q : Momentum) : ℝ := ‖(WithLp.toLp 2 q : EuclideanSpace ℝ Direction)‖

def incrementVector (c q : Momentum) (f : Frequency) : EuclideanSpace ℂ Direction :=
  WithLp.toLp 2 (fun j => symbol (c+q) f j - symbol c f j)

def linearVector (c q : Momentum) (f : Frequency) : EuclideanSpace ℂ Direction :=
  WithLp.toLp 2 (linearSymbol c q f)

theorem momentumNorm_sq (q : Momentum) : momentumNorm q^2 = ∑ j, (q j)^2 :=
  EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 q)

/-- The exponential symbol increment has the Euclidean momentum radius as
its Lipschitz constant; this bound is independent of the Fourier frequency. -/
theorem incrementVector_norm (c q : Momentum) (f : Frequency) :
    ‖incrementVector c q f‖ ≤ phaseScale * momentumNorm q := by
  have hsq : ‖incrementVector c q f‖^2 ≤ (phaseScale * momentumNorm q)^2 := by
    rw [EuclideanSpace.norm_sq_eq, mul_pow, momentumNorm_sq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have h := symbol_increment_bound c q f j
    calc
      ‖incrementVector c q f j‖^2 ≤ (phaseScale * |q j|)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = phaseScale^2 * (q j)^2 := by rw [mul_pow, sq_abs]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg phaseScale_pos.le (norm_nonneg _))).mp hsq

/-- The full three-component symbol has the same one-half quadratic
remainder constant as each exponential, without a dimension loss. -/
theorem incrementVector_linear_remainder (c q : Momentum) (f : Frequency) :
    ‖incrementVector c q f - linearVector c q f‖ ≤
      phaseScale^2 * momentumNorm q^2 / 2 := by
  have hfour : (∑ j, (q j)^4) ≤ (∑ j, (q j)^2)^2 := by
    have h := Finset.sum_sq_le_sq_sum_of_nonneg
      (s := (Finset.univ : Finset Direction)) (f := fun j => (q j)^2)
      (fun j _ => sq_nonneg (q j))
    simpa only [← pow_mul] using h
  have hsq : ‖incrementVector c q f - linearVector c q f‖^2 ≤
      (phaseScale^2 * momentumNorm q^2 / 2)^2 := by
    calc
      ‖incrementVector c q f - linearVector c q f‖^2
          ≤ ∑ j, (phaseScale^2 * (q j)^2 / 2)^2 := by
        rw [EuclideanSpace.norm_sq_eq]
        apply Finset.sum_le_sum
        intro j _
        exact pow_le_pow_left₀ (norm_nonneg _) (symbol_linear_remainder_bound c q f j) 2
      _ = phaseScale^4 / 4 * ∑ j, (q j)^4 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ phaseScale^4 / 4 * (∑ j, (q j)^2)^2 :=
        mul_le_mul_of_nonneg_left hfour (by positivity)
      _ = (phaseScale^2 * momentumNorm q^2 / 2)^2 := by
        rw [momentumNorm_sq]
        ring
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsq

end
end Maxwell.Spectral.BoxSymbols
