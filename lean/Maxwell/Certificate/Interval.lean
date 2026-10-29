import Mathlib.Data.Rat.Floor
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Exact rational enclosures with real semantics. All arithmetic uses Lean's
unbounded integers and rationals, so no machine-overflow premise is needed.
The witness producer can be untrusted: enclosure acceptance is checked below. -/
namespace Maxwell.Certificate

structure Interval where
  lo : ℚ
  hi : ℚ
  ordered : lo ≤ hi

namespace Interval

def Contains (a : Interval) (x : ℝ) : Prop := (a.lo : ℝ) ≤ x ∧ x ≤ (a.hi : ℝ)

def point (q : ℚ) : Interval := ⟨q, q, le_rfl⟩

def add (a b : Interval) : Interval :=
  ⟨a.lo + b.lo, a.hi + b.hi, add_le_add a.ordered b.ordered⟩

def neg (a : Interval) : Interval := ⟨-a.hi, -a.lo, neg_le_neg a.ordered⟩

theorem contains_point (q : ℚ) : (point q).Contains q := ⟨le_rfl, le_rfl⟩

theorem contains_add {a b : Interval} {x y : ℝ}
    (ha : a.Contains x) (hb : b.Contains y) : (add a b).Contains (x + y) := by
  simpa [Contains, add] using And.intro (add_le_add ha.1 hb.1) (add_le_add ha.2 hb.2)

theorem contains_neg {a : Interval} {x : ℝ} (ha : a.Contains x) :
    (neg a).Contains (-x) := by
  simpa [Contains, neg] using And.intro (neg_le_neg ha.2) (neg_le_neg ha.1)

/-- An explicit finite acceptance predicate; only the endpoints are checked. -/
def subsetCheck (a b : Interval) : Bool := decide (b.lo ≤ a.lo ∧ a.hi ≤ b.hi)

theorem subsetCheck_sound {a b : Interval} (h : subsetCheck a b = true)
    {x : ℝ} (hx : a.Contains x) : b.Contains x := by
  have hq : b.lo ≤ a.lo ∧ a.hi ≤ b.hi := of_decide_eq_true h
  exact ⟨(Rat.cast_le.mpr hq.1).trans hx.1, hx.2.trans (Rat.cast_le.mpr hq.2)⟩

def lowerCheck (a : Interval) (q : ℚ) : Bool := decide (q < a.lo)

theorem lowerCheck_sound {a : Interval} {q : ℚ} (h : lowerCheck a q = true)
    {x : ℝ} (hx : a.Contains x) : (q : ℝ) < x :=
  (Rat.cast_lt.mpr (of_decide_eq_true h)).trans_le hx.1

/-- Outward rounding to the exact dyadic grid of denominator `2^p`. -/
def roundOut (p : ℕ) (a : Interval) : Interval where
  lo := (Int.floor (a.lo * (2 : ℚ)^p) : ℚ) / (2 : ℚ)^p
  hi := (Int.ceil (a.hi * (2 : ℚ)^p) : ℚ) / (2 : ℚ)^p
  ordered := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact (Int.floor_le _).trans ((mul_le_mul_of_nonneg_right a.ordered (by positivity)).trans (Int.le_ceil _))

theorem roundOut_contains {a : Interval} {x : ℝ} (p : ℕ) (ha : a.Contains x) :
    (roundOut p a).Contains x := by
  have hp : (0 : ℚ) < 2^p := by positivity
  have hlo : (roundOut p a).lo ≤ a.lo := by
    exact (div_le_iff₀ hp).mpr (Int.floor_le _)
  have hhi : a.hi ≤ (roundOut p a).hi := by
    exact (le_div_iff₀ hp).mpr (Int.le_ceil _)
  exact ⟨(Rat.cast_le.mpr hlo).trans ha.1, ha.2.trans (Rat.cast_le.mpr hhi)⟩

end Interval

/-- Rational midpoint/radius enclosures; both real and imaginary channels
of a complex rectangle can use this same verified scalar operation. -/
structure Ball where
  center : ℚ
  radius : ℚ
  radius_nonneg : 0 ≤ radius

namespace Ball

def Contains (a : Ball) (x : ℝ) : Prop := |x - (a.center : ℝ)| ≤ (a.radius : ℝ)

def add (a b : Ball) : Ball :=
  ⟨a.center + b.center, a.radius + b.radius, add_nonneg a.radius_nonneg b.radius_nonneg⟩

def mul (a b : Ball) : Ball where
  center := a.center * b.center
  radius := |a.center| * b.radius + |b.center| * a.radius + a.radius * b.radius
  radius_nonneg := add_nonneg (add_nonneg (mul_nonneg (abs_nonneg _) b.radius_nonneg) (mul_nonneg (abs_nonneg _) a.radius_nonneg)) (mul_nonneg a.radius_nonneg b.radius_nonneg)

theorem contains_add {a b : Ball} {x y : ℝ}
    (ha : a.Contains x) (hb : b.Contains y) : (add a b).Contains (x + y) := by
  dsimp [Contains, add] at *
  push_cast
  calc
    |x + y - ((a.center : ℝ) + b.center)| = |(x - a.center) + (y - b.center)| := by ring_nf
    _ ≤ |x - a.center| + |y - b.center| := abs_add_le _ _
    _ ≤ (a.radius : ℝ) + b.radius := add_le_add ha hb

theorem contains_mul {a b : Ball} {x y : ℝ}
    (ha : a.Contains x) (hb : b.Contains y) : (mul a b).Contains (x * y) := by
  have h_ar : (0 : ℝ) ≤ a.radius := Rat.cast_nonneg.mpr a.radius_nonneg
  have h_br : (0 : ℝ) ≤ b.radius := Rat.cast_nonneg.mpr b.radius_nonneg
  dsimp [Contains] at ha hb
  dsimp [Contains, mul]
  push_cast
  calc
    |x * y - (a.center : ℝ) * b.center| =
        |(a.center : ℝ) * (y - b.center) + (b.center : ℝ) * (x - a.center) +
          (x - a.center) * (y - b.center)| := by congr 1; ring
    _ ≤ |(a.center : ℝ) * (y - b.center)| + |(b.center : ℝ) * (x - a.center)| +
          |(x - a.center) * (y - b.center)| := abs_add_three _ _ _
    _ ≤ |(a.center : ℝ)| * b.radius + |(b.center : ℝ)| * a.radius +
          (a.radius : ℝ) * b.radius := by
      simp only [abs_mul]
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hb (abs_nonneg _))
        (mul_le_mul_of_nonneg_left ha (abs_nonneg _)))
        (mul_le_mul ha hb (abs_nonneg _) h_ar)

end Ball
end Maxwell.Certificate
