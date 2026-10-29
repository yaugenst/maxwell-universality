import Maxwell.Certificate.FFTInterval

/-! Unconditional 52-bit enclosures for the FCC FFT constants. Square-root
bounds are checked by exact rational arithmetic; roots of unity use the proved
trigonometric evaluator. No floating-point root or normalization is assumed. -/

namespace Maxwell.Certificate.FFTInterval

open Matrix FourierBinding Maxwell.Spectral.PrimitiveYee

def sqrt10Interval : Interval :=
  ⟨58333726687135158848 / (2 : ℚ)^64, 58333726687135158849 / (2 : ℚ)^64, by norm_num⟩

def sqrt20Interval : Interval :=
  ⟨82496347424711897175 / (2 : ℚ)^64, 82496347424711897176 / (2 : ℚ)^64, by norm_num⟩

theorem sqrt10_checked : Interval.sqrtCheck (Interval.point 10) sqrt10Interval = true := by
  decide +kernel

theorem sqrt20_checked : Interval.sqrtCheck (Interval.point 20) sqrt20Interval = true := by
  decide +kernel

def norm10 : Ball := Trigonometric.roundBall 52 (Trigonometric.intervalToBall
  (Interval.reciprocal sqrt10Interval (by norm_num [sqrt10Interval])))

def norm20 : Ball := Trigonometric.roundBall 52 (Trigonometric.intervalToBall
  (Interval.reciprocal sqrt20Interval (by norm_num [sqrt20Interval])))

theorem norm10_contains : norm10.Contains (1 / Real.sqrt 10) :=
  Trigonometric.roundBall_contains 52 (Trigonometric.intervalToBall_contains
    (Interval.reciprocal_contains _
      (Interval.sqrtCheck_sound sqrt10_checked (Interval.contains_point 10))))

theorem norm20_contains : norm20.Contains (1 / Real.sqrt 20) :=
  Trigonometric.roundBall_contains 52 (Trigonometric.intervalToBall_contains
    (Interval.reciprocal_contains _
      (Interval.sqrtCheck_sound sqrt20_checked (Interval.contains_point 20))))

def root (m : ℤ) : ComplexRectangle :=
  Trigonometric.roundedCisRectangle 52 (((m % 20 : ℤ) : ℚ) / 20)

theorem root_contains (m : ℤ) : (root m).Contains (root20 m) :=
  Trigonometric.roundedCisRectangle_contains 52 _

def kernel20 : IntervalLinear.Rectangular 20 20 := fun a b =>
  IntervalLinear.round 52
    ((IntervalMatrix.realRectangle norm20).mul (root ((a.val : ℤ) * b.val)).conjugate)

def kernel10 : IntervalLinear.Rectangular 10 10 := fun a b =>
  IntervalLinear.round 52
    ((IntervalMatrix.realRectangle norm10).mul (root (2 * (a.val : ℤ) * b.val)).conjugate)

theorem kernel20_contains : IntervalLinear.Contains kernel20 (cyclicFourier 20) := by
  intro a b
  rw [cyclicFourier_twenty_root]
  apply IntervalLinear.round_contains
  have h := ComplexRectangle.contains_mul (IntervalMatrix.realRectangle_contains norm20_contains)
    (ComplexRectangle.contains_conjugate (root_contains ((a.val : ℤ) * b.val)))
  simpa only [Complex.ofReal_div, Complex.ofReal_one, one_div,
    Complex.ofReal_inv, one_mul] using h

theorem kernel10_contains : IntervalLinear.Contains kernel10 (cyclicFourier 10) := by
  intro a b
  rw [cyclicFourier_ten_root]
  apply IntervalLinear.round_contains
  have h := ComplexRectangle.contains_mul (IntervalMatrix.realRectangle_contains norm10_contains)
    (ComplexRectangle.contains_conjugate (root_contains (2 * (a.val : ℤ) * b.val)))
  simpa only [Complex.ofReal_div, Complex.ofReal_one, one_div,
    Complex.ofReal_inv, one_mul] using h

def twiddle : Field := fun p => root ((p.1.val : ℤ) * (p.2.1.val + p.2.2.val))

theorem twiddle_contains : Contains twiddle fccTwiddle := by
  intro p
  rw [fccTwiddle_eq_root]
  exact root_contains _

theorem checked_forward (input : Field) (w : Proposal) (v : Cell → ℂ)
    (hv : Contains input v) (h : forwardCheck kernel20 kernel10 twiddle input w = true) :
    Contains w.result ((transform 0).conjTranspose *ᵥ v) :=
  forwardCheck_sound _ _ _ _ _ kernel20_contains kernel10_contains twiddle_contains _ hv h

theorem checked_inverse (input : Field) (w : Proposal) (v : Cell → ℂ)
    (hv : Contains input v) (h : inverseCheck kernel20 kernel10 twiddle input w = true) :
    Contains w.result (transform 0 *ᵥ v) :=
  inverseCheck_sound _ _ _ _ _ kernel20_contains kernel10_contains twiddle_contains _ hv h

theorem checked_rational_forward (v : Cell → ℚ × ℚ) (w : Proposal)
    (h : forwardCheck kernel20 kernel10 twiddle (fun p => pointRectangle (v p)) w = true) :
    Contains w.result ((transform 0).conjTranspose *ᵥ fun p => Trigonometric.toComplex (v p)) :=
  checked_forward _ w _ (fun p => pointRectangle_contains (v p)) h

theorem checked_rational_inverse (v : Cell → ℚ × ℚ) (w : Proposal)
    (h : inverseCheck kernel20 kernel10 twiddle (fun p => pointRectangle (v p)) w = true) :
    Contains w.result (transform 0 *ᵥ fun p => Trigonometric.toComplex (v p)) :=
  checked_inverse _ w _ (fun p => pointRectangle_contains (v p)) h

end Maxwell.Certificate.FFTInterval
