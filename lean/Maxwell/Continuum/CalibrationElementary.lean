import Maxwell.Certificate.Elementary
import Maxwell.Continuum.CalibrationTaylorBound
import Mathlib.Analysis.Complex.Trigonometric

/-! Executable rational Taylor enclosures, using the existing certificate
rectangle arithmetic. The result encloses the actual exponential, sine,
or cosine; all coefficients and error radii are rational. -/

namespace Maxwell.Certificate

namespace ComplexRectangle

def point (a b : ℚ) : ComplexRectangle :=
  ⟨⟨a,0,le_rfl⟩,⟨b,0,le_rfl⟩⟩

theorem contains_point (a b : ℚ) : (point a b).Contains ((a : ℂ)+(b : ℂ)*Complex.I) := by
  simp [Contains,point,Ball.Contains]

def power (a : ComplexRectangle) : ℕ → ComplexRectangle
  | 0 => point 1 0
  | n+1 => mul (power a n) a

theorem contains_power {a : ComplexRectangle} {z : ℂ} (hz : a.Contains z) (n : ℕ) :
    (power a n).Contains (z^n) := by
  induction n with
  | zero => simpa [power] using contains_point 1 0
  | succ n ih => simpa [power,pow_succ] using contains_mul ih hz

def expTaylor (a : ComplexRectangle) : ℕ → ComplexRectangle
  | 0 => point 0 0
  | n+1 => add (expTaylor a n) (mul (power a n) (point (1/(n.factorial : ℚ)) 0))

theorem expTaylor_contains {a : ComplexRectangle} {z : ℂ} (hz : a.Contains z) (n : ℕ) :
    (expTaylor a n).Contains (∑ k ∈ Finset.range n, z^k/(k.factorial : ℂ)) := by
  induction n with
  | zero => simpa [expTaylor] using contains_point 0 0
  | succ n ih =>
    have hp := contains_mul (contains_power hz n) (contains_point (1/(n.factorial : ℚ)) 0)
    simpa [expTaylor,Finset.sum_range_succ,div_eq_mul_inv] using contains_add ih hp

def enlarge (a : ComplexRectangle) (ε : ℚ) (hε : 0 ≤ ε) : ComplexRectangle :=
  ⟨⟨a.re.center,a.re.radius+ε,add_nonneg a.re.radius_nonneg hε⟩,
   ⟨a.im.center,a.im.radius+ε,add_nonneg a.im.radius_nonneg hε⟩⟩

theorem enlarge_contains {a : ComplexRectangle} {z w : ℂ} (hz : a.Contains z)
    {ε : ℚ} (hε : 0 ≤ ε) (h : ‖w-z‖ ≤ (ε : ℝ)) : (enlarge a ε hε).Contains w := by
  constructor
  · change |w.re-(a.re.center : ℝ)| ≤ ((a.re.radius+ε : ℚ) : ℝ)
    rw [Rat.cast_add]
    calc
      _ ≤ |w.re-z.re|+|z.re-(a.re.center : ℝ)| := abs_sub_le _ _ _
      _ ≤ (ε : ℝ)+(a.re.radius : ℝ) := add_le_add
        ((Complex.abs_re_le_norm (w-z)).trans h) hz.1
      _ = _ := add_comm _ _
  · change |w.im-(a.im.center : ℝ)| ≤ ((a.im.radius+ε : ℚ) : ℝ)
    rw [Rat.cast_add]
    calc
      _ ≤ |w.im-z.im|+|z.im-(a.im.center : ℝ)| := abs_sub_le _ _ _
      _ ≤ (ε : ℝ)+(a.im.radius : ℝ) := add_le_add
        ((Complex.abs_im_le_norm (w-z)).trans h) hz.2
      _ = _ := add_comm _ _

def expEnclosure (a : ComplexRectangle) (B N : ℕ) : ComplexRectangle :=
  enlarge (expTaylor a (Maxwell.Continuum.Calibration.taylorOrder B N))
    ((1/2 : ℚ)^N) (by positivity)

theorem expEnclosure_contains {a : ComplexRectangle} {z : ℂ} (hz : a.Contains z)
    (B N : ℕ) (hB : ‖z‖ ≤ B) : (expEnclosure a B N).Contains (Complex.exp z) := by
  apply enlarge_contains (expTaylor_contains hz _) (by positivity)
  simpa only [Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
    Maxwell.Continuum.Calibration.taylor_remainder_bound B N hB

theorem power_radii_zero {a : ComplexRectangle}
    (ha : a.re.radius = 0 ∧ a.im.radius = 0) (n : ℕ) :
    (power a n).re.radius = 0 ∧ (power a n).im.radius = 0 := by
  induction n with
  | zero => simp [power,point]
  | succ n ih => simp [power,mul,Ball.add,Ball.mul,Ball.neg,ha.1,ha.2,ih.1,ih.2]

theorem expTaylor_radii_zero {a : ComplexRectangle}
    (ha : a.re.radius = 0 ∧ a.im.radius = 0) (n : ℕ) :
    (expTaylor a n).re.radius = 0 ∧ (expTaylor a n).im.radius = 0 := by
  induction n with
  | zero => simp [expTaylor,point]
  | succ n ih =>
    have hp := power_radii_zero ha n
    simp [expTaylor,add,mul,Ball.add,Ball.mul,Ball.neg,point,ih.1,ih.2,hp.1,hp.2]

theorem expEnclosure_point_radii (a b : ℚ) (B N : ℕ) :
    (expEnclosure (point a b) B N).re.radius = (1/2 : ℚ)^N ∧
    (expEnclosure (point a b) B N).im.radius = (1/2 : ℚ)^N := by
  have h := expTaylor_radii_zero (a := point a b) ⟨rfl,rfl⟩
    (Maxwell.Continuum.Calibration.taylorOrder B N)
  simp [expEnclosure,enlarge,h.1,h.2]

end ComplexRectangle

namespace Elementary

def expApprox (q : ℚ) (B N : ℕ) : Ball :=
  (ComplexRectangle.expEnclosure (ComplexRectangle.point q 0) B N).re

def cosApprox (q : ℚ) (B N : ℕ) : Ball :=
  (ComplexRectangle.expEnclosure (ComplexRectangle.point 0 q) B N).re

def sinApprox (q : ℚ) (B N : ℕ) : Ball :=
  (ComplexRectangle.expEnclosure (ComplexRectangle.point 0 q) B N).im

theorem expApprox_contains (q : ℚ) (B N : ℕ) (hq : |q| ≤ B) :
    (expApprox q B N).Contains (Real.exp q) := by
  have hp : (ComplexRectangle.point q 0).Contains ((q : ℝ) : ℂ) := by
    simpa using ComplexRectangle.contains_point q 0
  have hqr : |(q : ℝ)| ≤ (B : ℝ) := by exact_mod_cast hq
  have hB : ‖((q : ℝ) : ℂ)‖ ≤ B := by simpa using hqr
  have h := (ComplexRectangle.expEnclosure_contains hp B N hB).1
  simpa only [expApprox,Complex.exp_ofReal_re] using h

theorem cosApprox_contains (q : ℚ) (B N : ℕ) (hq : |q| ≤ B) :
    (cosApprox q B N).Contains (Real.cos q) := by
  have hp : (ComplexRectangle.point 0 q).Contains (((q : ℝ) : ℂ)*Complex.I) := by
    simpa using ComplexRectangle.contains_point 0 q
  have hqr : |(q : ℝ)| ≤ (B : ℝ) := by exact_mod_cast hq
  have hB : ‖((q : ℝ) : ℂ)*Complex.I‖ ≤ B := by simpa [norm_mul] using hqr
  have h := (ComplexRectangle.expEnclosure_contains hp B N hB).1
  simpa only [cosApprox,Complex.exp_ofReal_mul_I_re] using h

theorem sinApprox_contains (q : ℚ) (B N : ℕ) (hq : |q| ≤ B) :
    (sinApprox q B N).Contains (Real.sin q) := by
  have hp : (ComplexRectangle.point 0 q).Contains (((q : ℝ) : ℂ)*Complex.I) := by
    simpa using ComplexRectangle.contains_point 0 q
  have hqr : |(q : ℝ)| ≤ (B : ℝ) := by exact_mod_cast hq
  have hB : ‖((q : ℝ) : ℂ)*Complex.I‖ ≤ B := by simpa [norm_mul] using hqr
  have h := (ComplexRectangle.expEnclosure_contains hp B N hB).2
  simpa only [sinApprox,Complex.exp_ofReal_mul_I_im] using h

theorem elementary_radii (q : ℚ) (B N : ℕ) :
    (expApprox q B N).radius = (1/2 : ℚ)^N ∧
    (cosApprox q B N).radius = (1/2 : ℚ)^N ∧
    (sinApprox q B N).radius = (1/2 : ℚ)^N :=
  ⟨(ComplexRectangle.expEnclosure_point_radii q 0 B N).1,
   (ComplexRectangle.expEnclosure_point_radii 0 q B N).1,
   (ComplexRectangle.expEnclosure_point_radii 0 q B N).2⟩

#print axioms expApprox_contains
#print axioms cosApprox_contains
#print axioms sinApprox_contains
#print axioms elementary_radii

end Elementary
end Maxwell.Certificate
