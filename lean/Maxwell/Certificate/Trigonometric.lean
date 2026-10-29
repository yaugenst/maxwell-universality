import Maxwell.Certificate.Elementary
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Rational enclosures of Fourier phases. The center is an exact rational
Taylor polynomial; the radius includes both a proved pi enclosure and the
complex exponential remainder. No floating-point trigonometric value is trusted. -/

namespace Maxwell.Certificate.Trigonometric

def piMid : ℚ := 3141592653589793238465 / 10 ^ 21
def piRadius : ℚ := 5 / 10 ^ 21

theorem pi_enclosed : |Real.pi - (piMid : ℝ)| ≤ (piRadius : ℝ) := by
  have hlo := Real.pi_gt_d20
  have hhi := Real.pi_lt_d20
  norm_num [piMid, piRadius] at ⊢
  rw [abs_le]
  constructor <;> linarith

def reducedPhase (q : ℚ) : ℚ := q - (Int.floor (q + 1 / 2) : ℚ)

theorem reducedPhase_bounds (q : ℚ) : -(1 / 2) ≤ reducedPhase q ∧ reducedPhase q ≤ 1 / 2 := by
  have hlo := Int.floor_le (q + 1 / 2)
  have hhi := Int.lt_floor_add_one (q + 1 / 2)
  unfold reducedPhase
  constructor <;> linarith

noncomputable def cis (q : ℚ) : ℂ :=
  Complex.exp (Complex.I * ((2 * Real.pi * (q : ℝ)) : ℂ))

theorem cis_reducedPhase (q : ℚ) : cis q = cis (reducedPhase q) := by
  have he : Complex.I * ((2 * Real.pi * (q : ℝ)) : ℂ) =
      Complex.I * ((2 * Real.pi * (reducedPhase q : ℝ)) : ℂ) +
        (Int.floor (q + 1 / 2) : ℂ) * (2 * Real.pi * Complex.I) := by
    unfold reducedPhase
    push_cast
    ring
  unfold cis
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Rational real/imaginary parts of `(i*x)^n`. -/
def imaginaryPower (x : ℚ) : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | n + 1 => (-x * (imaginaryPower x n).2, x * (imaginaryPower x n).1)

noncomputable def toComplex (a : ℚ × ℚ) : ℂ := (a.1 : ℂ) + Complex.I * (a.2 : ℂ)

theorem imaginaryPower_binding (x : ℚ) (n : ℕ) :
    toComplex (imaginaryPower x n) = (Complex.I * (x : ℂ)) ^ n := by
  induction n with
  | zero => simp [imaginaryPower, toComplex]
  | succ n ih =>
      rw [pow_succ', ← ih]
      simp only [imaginaryPower, toComplex, Rat.cast_mul, Rat.cast_neg]
      ring_nf
      simp [Complex.I_sq]

def taylorCenter (x : ℚ) (n : ℕ) : ℚ × ℚ :=
  (∑ j ∈ Finset.range n, (imaginaryPower x j).1 / (j.factorial : ℚ),
   ∑ j ∈ Finset.range n, (imaginaryPower x j).2 / (j.factorial : ℚ))

theorem taylorCenter_binding (x : ℚ) (n : ℕ) :
    toComplex (taylorCenter x n) =
      ∑ j ∈ Finset.range n, (Complex.I * (x : ℂ)) ^ j / (j.factorial : ℂ) := by
  simp only [toComplex, taylorCenter, Rat.cast_sum, Rat.cast_div, Rat.cast_natCast,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← imaginaryPower_binding]
  dsimp [toComplex]
  ring

def remainder (n : ℕ) : ℚ := 2 * 4 ^ n / (n.factorial : ℚ)

theorem remainder_nonneg (n : ℕ) : 0 ≤ remainder n := by
  unfold remainder
  positivity

theorem taylorCenter_error (x : ℚ) (hx : |x| ≤ 4) (n : ℕ) (hn : 7 ≤ n) :
    ‖Complex.exp (Complex.I * (x : ℂ)) - toComplex (taylorCenter x n)‖ ≤
      (remainder n : ℝ) := by
  have hxR : |(x : ℝ)| ≤ 4 := by exact_mod_cast hx
  have hnorm : ‖Complex.I * (x : ℂ)‖ ≤ 4 := by
    simpa using hxR
  have hnR : (8 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast (show 8 ≤ n + 1 by omega)
  have hdiv : ‖Complex.I * (x : ℂ)‖ / (n + 1 : ℕ) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n + 1 : ℕ))).mpr
    linarith
  rw [taylorCenter_binding]
  calc
    _ ≤ ‖Complex.I * (x : ℂ)‖ ^ n / (n.factorial : ℝ) * 2 := Complex.exp_bound' hdiv
    _ ≤ 4 ^ n / (n.factorial : ℝ) * 2 :=
      mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hnorm n)
          (by positivity)) (by norm_num)
    _ = (remainder n : ℝ) := by push_cast [remainder]; ring

theorem imaginary_exp_lipschitz (x y : ℝ) :
    ‖Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (Complex.I * (y : ℂ))‖ ≤
      |x - y| := by
  have he : Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (Complex.I * (y : ℂ)) =
      Complex.exp (Complex.I * (y : ℂ)) *
        (Complex.exp (Complex.I * ((x - y : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 2
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

def reducedAngle (q : ℚ) : ℚ := 2 * piMid * reducedPhase q

theorem reducedAngle_bound (q : ℚ) : |reducedAngle q| ≤ 4 := by
  have hf := reducedPhase_bounds q
  have hp : 0 ≤ piMid ∧ piMid ≤ 4 := by norm_num [piMid]
  rw [reducedAngle, abs_mul, abs_mul]
  norm_num [abs_of_nonneg hp.1]
  have hfabs : |reducedPhase q| ≤ 1 / 2 := abs_le.mpr hf
  nlinarith

theorem reducedAngle_error (q : ℚ) :
    |2 * Real.pi * (reducedPhase q : ℝ) - (reducedAngle q : ℝ)| ≤
      (piRadius : ℝ) := by
  have hf : |(reducedPhase q : ℝ)| ≤ 1 / 2 := by
    rw [abs_le]
    constructor
    · simpa only [Rat.cast_neg, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
        (Rat.cast_le.mpr (reducedPhase_bounds q).1 :
          ((-(1 / 2) : ℚ) : ℝ) ≤ (reducedPhase q : ℝ))
    · simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
        (Rat.cast_le.mpr (reducedPhase_bounds q).2 :
          (reducedPhase q : ℝ) ≤ ((1 / 2 : ℚ) : ℝ))
  have hp : (0 : ℝ) ≤ piRadius := by norm_num [piRadius]
  calc
    _ = 2 * |Real.pi - (piMid : ℝ)| * |(reducedPhase q : ℝ)| := by
      simp only [reducedAngle, Rat.cast_mul, Rat.cast_ofNat]
      rw [show 2 * Real.pi * (reducedPhase q : ℝ) -
        2 * (piMid : ℝ) * (reducedPhase q : ℝ) =
        2 * (Real.pi - (piMid : ℝ)) * (reducedPhase q : ℝ) by ring]
      simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ 2 * (piRadius : ℝ) * (1 / 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left pi_enclosed (by norm_num)) hf
        (abs_nonneg _) (mul_nonneg (by norm_num) hp)
    _ = _ := by ring

def cisRadius : ℚ := piRadius + remainder 64

theorem cisRadius_nonneg : 0 ≤ cisRadius :=
  add_nonneg (by norm_num [piRadius]) (remainder_nonneg _)

theorem cisRadius_precision : cisRadius < (2 : ℚ) ^ (-66 : ℤ) := by
  norm_num [cisRadius, piRadius, remainder, Nat.factorial]

theorem cisCenter_error (q : ℚ) :
    ‖cis q - toComplex (taylorCenter (reducedAngle q) 64)‖ ≤ (cisRadius : ℝ) := by
  rw [cis_reducedPhase]
  calc
    _ ≤ ‖cis (reducedPhase q) - Complex.exp (Complex.I * (reducedAngle q : ℂ))‖ +
        ‖Complex.exp (Complex.I * (reducedAngle q : ℂ)) -
          toComplex (taylorCenter (reducedAngle q) 64)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (piRadius : ℝ) + (remainder 64 : ℝ) := add_le_add
      (by simpa only [cis, Complex.ofReal_ratCast, Complex.ofReal_mul,
          Complex.ofReal_ofNat] using
        ((imaginary_exp_lipschitz _ _).trans (reducedAngle_error q)))
      (taylorCenter_error _ (reducedAngle_bound q) _ (by norm_num))
    _ = _ := by simp only [cisRadius, Rat.cast_add]

def cisRectangle (q : ℚ) : ComplexRectangle where
  re := ⟨(taylorCenter (reducedAngle q) 64).1, cisRadius, cisRadius_nonneg⟩
  im := ⟨(taylorCenter (reducedAngle q) 64).2, cisRadius, cisRadius_nonneg⟩

theorem cisRectangle_contains (q : ℚ) : (cisRectangle q).Contains (cis q) := by
  have h := cisCenter_error q
  constructor
  · have hr := (Complex.abs_re_le_norm
      (cis q - toComplex (taylorCenter (reducedAngle q) 64))).trans h
    simpa [Ball.Contains, cisRectangle, toComplex] using hr
  · have hi := (Complex.abs_im_le_norm
      (cis q - toComplex (taylorCenter (reducedAngle q) 64))).trans h
    simpa [Ball.Contains, cisRectangle, toComplex] using hi

theorem cis_re (q : ℚ) : (cis q).re = Real.cos (2 * Real.pi * (q : ℝ)) := by
  simp [cis, Complex.exp_re]

theorem cis_im (q : ℚ) : (cis q).im = Real.sin (2 * Real.pi * (q : ℝ)) := by
  simp [cis, Complex.exp_im]

theorem cosine_contains (q : ℚ) :
    (cisRectangle q).re.Contains (Real.cos (2 * Real.pi * (q : ℝ))) := by
  rw [← cis_re]
  exact (cisRectangle_contains q).1

theorem sine_contains (q : ℚ) :
    (cisRectangle q).im.Contains (Real.sin (2 * Real.pi * (q : ℝ))) := by
  rw [← cis_im]
  exact (cisRectangle_contains q).2

def ballToInterval (a : Ball) : Interval :=
  ⟨a.center - a.radius, a.center + a.radius, by linarith [a.radius_nonneg]⟩

theorem ballToInterval_contains {a : Ball} {x : ℝ} (h : a.Contains x) :
    (ballToInterval a).Contains x := by
  rw [Ball.Contains, abs_le] at h
  simp only [Interval.Contains, ballToInterval, Rat.cast_sub, Rat.cast_add]
  constructor <;> linarith [h.1, h.2]

def intervalToBall (a : Interval) : Ball :=
  ⟨(a.lo + a.hi) / 2, (a.hi - a.lo) / 2, by linarith [a.ordered]⟩

theorem intervalToBall_contains {a : Interval} {x : ℝ} (h : a.Contains x) :
    (intervalToBall a).Contains x := by
  simp only [Ball.Contains, intervalToBall, Rat.cast_div, Rat.cast_add, Rat.cast_sub,
    Rat.cast_ofNat, abs_le]
  constructor <;> linarith [h.1, h.2]

def roundBall (p : ℕ) (a : Ball) : Ball :=
  intervalToBall (Interval.roundOut p (ballToInterval a))

theorem roundBall_contains {a : Ball} {x : ℝ} (p : ℕ) (h : a.Contains x) :
    (roundBall p a).Contains x :=
  intervalToBall_contains (Interval.roundOut_contains p (ballToInterval_contains h))

theorem roundBall_radius (p : ℕ) (a : Ball) :
    (roundBall p a).radius < a.radius + 1 / (2 : ℚ) ^ p := by
  have hp : (0 : ℚ) < 2 ^ p := by positivity
  have hlo := div_lt_div_of_pos_right (Int.sub_one_lt_floor
    ((a.center - a.radius) * (2 : ℚ) ^ p)) hp
  have hhi := div_lt_div_of_pos_right (Int.ceil_lt_add_one
    ((a.center + a.radius) * (2 : ℚ) ^ p)) hp
  simp only [sub_div, add_div, mul_div_cancel_right₀ _ (ne_of_gt hp)] at hlo hhi
  dsimp [roundBall, intervalToBall, Interval.roundOut, ballToInterval]
  linarith

def roundedCisRectangle (p : ℕ) (q : ℚ) : ComplexRectangle :=
  ⟨roundBall p (cisRectangle q).re, roundBall p (cisRectangle q).im⟩

theorem roundedCisRectangle_contains (p : ℕ) (q : ℚ) :
    (roundedCisRectangle p q).Contains (cis q) :=
  ⟨roundBall_contains p (cisRectangle_contains q).1,
   roundBall_contains p (cisRectangle_contains q).2⟩

theorem roundedCisRectangle_precision (p : ℕ) (q : ℚ) :
    (roundedCisRectangle p q).re.radius < (2 : ℚ) ^ (-66 : ℤ) + 1 / (2 : ℚ) ^ p ∧
    (roundedCisRectangle p q).im.radius < (2 : ℚ) ^ (-66 : ℤ) + 1 / (2 : ℚ) ^ p := by
  constructor
  · have h := roundBall_radius p (cisRectangle q).re
    change (roundedCisRectangle p q).re.radius < cisRadius + 1 / (2 : ℚ) ^ p at h
    exact lt_trans h (add_lt_add_of_lt_of_le cisRadius_precision le_rfl)
  · have h := roundBall_radius p (cisRectangle q).im
    change (roundedCisRectangle p q).im.radius < cisRadius + 1 / (2 : ℚ) ^ p at h
    exact lt_trans h (add_lt_add_of_lt_of_le cisRadius_precision le_rfl)

/-- Exact rational acceptance of a proposed enclosure. -/
def ballSubsetCheck (a b : Ball) : Bool :=
  decide (|a.center - b.center| + a.radius ≤ b.radius)

theorem ballSubsetCheck_sound {a b : Ball} (h : ballSubsetCheck a b = true)
    {x : ℝ} (hx : a.Contains x) : b.Contains x := by
  have hq : |a.center - b.center| + a.radius ≤ b.radius := of_decide_eq_true h
  have hr : |(a.center : ℝ) - b.center| + (a.radius : ℝ) ≤ b.radius := by
    exact_mod_cast hq
  calc
    |x - (b.center : ℝ)| = |(x - a.center) + ((a.center : ℝ) - b.center)| := by ring_nf
    _ ≤ |x - (a.center : ℝ)| + |(a.center : ℝ) - b.center| := abs_add_le _ _
    _ ≤ (b.radius : ℝ) := by dsimp [Ball.Contains] at hx; linarith

def rectangleSubsetCheck (a b : ComplexRectangle) : Bool :=
  ballSubsetCheck a.re b.re && ballSubsetCheck a.im b.im

theorem rectangleSubsetCheck_sound {a b : ComplexRectangle}
    (h : rectangleSubsetCheck a b = true) {z : ℂ} (hz : a.Contains z) : b.Contains z := by
  have hh : ballSubsetCheck a.re b.re = true ∧ ballSubsetCheck a.im b.im = true := by
    simpa only [rectangleSubsetCheck, Bool.and_eq_true_iff] using h
  exact ⟨ballSubsetCheck_sound hh.1 hz.1, ballSubsetCheck_sound hh.2 hz.2⟩

def cisCheck (q : ℚ) (proposed : ComplexRectangle) : Bool :=
  rectangleSubsetCheck (cisRectangle q) proposed

theorem cisCheck_sound {q : ℚ} {proposed : ComplexRectangle} (h : cisCheck q proposed = true) :
    proposed.Contains (cis q) := rectangleSubsetCheck_sound h (cisRectangle_contains q)

end Maxwell.Certificate.Trigonometric
