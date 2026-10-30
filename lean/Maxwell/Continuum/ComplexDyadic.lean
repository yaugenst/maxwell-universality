import Maxwell.Continuum.DyadicRounding
import Maxwell.Continuum.CalibrationGridPhase

/-! Complex fixed-point coefficients are pairs of the existing dyadic words. -/

namespace Maxwell.Continuum

open Maxwell.Certificate Calibration

abbrev ComplexDyadic (P : ℕ) := Dyadic P × Dyadic P

noncomputable def complexDyadicValue {P : ℕ} (a : ComplexDyadic P) : ℂ :=
  (a.1.value : ℂ)+(a.2.value : ℂ)*Complex.I

def roundComplex (P : ℕ) (a : ComplexRectangle) : ComplexDyadic P :=
  (roundDyadic P a.re.center, roundDyadic P a.im.center)

theorem roundComplex_error (P : ℕ) (a : ComplexRectangle) :
    ‖rectangleCenter a-complexDyadicValue (roundComplex P a)‖ ≤ 2*(1/2 : ℝ)^P := by
  have hr := roundDyadic_error P a.re.center
  have hi := roundDyadic_error P a.im.center
  apply (Complex.norm_le_abs_re_add_abs_im _).trans
  simp only [rectangleCenter, complexDyadicValue, roundComplex, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re,
    Complex.ratCast_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
    add_zero, zero_add]
  linarith

theorem complexDyadicValue_re {P : ℕ} (a : ComplexDyadic P) :
    (complexDyadicValue a).re=(a.1.value : ℝ) := by simp [complexDyadicValue]

theorem complexDyadicValue_im {P : ℕ} (a : ComplexDyadic P) :
    (complexDyadicValue a).im=(a.2.value : ℝ) := by simp [complexDyadicValue]

theorem complexDyadicValue_coordinate_bounds {P : ℕ} (a : ComplexDyadic P) {B : ℚ}
    (hB : ‖complexDyadicValue a‖≤(B : ℝ)) : |a.1.value|≤B ∧ |a.2.value|≤B := by
  have hr := (Complex.abs_re_le_norm (complexDyadicValue a)).trans hB
  have hi := (Complex.abs_im_le_norm (complexDyadicValue a)).trans hB
  rw [complexDyadicValue_re] at hr
  rw [complexDyadicValue_im] at hi
  constructor
  · exact_mod_cast hr
  · exact_mod_cast hi

#print axioms roundComplex_error

end Maxwell.Continuum
