import Maxwell.Certificate.Interval
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Basic.Complex.Basic

namespace Maxwell.Certificate
namespace Interval

def reciprocal (a : Interval) (h : 0 < a.lo) : Interval :=
  ⟨1 / a.hi, 1 / a.lo, one_div_le_one_div_of_le h a.ordered⟩

theorem reciprocal_contains {a : Interval} (h : 0 < a.lo) {x : ℝ}
    (hx : a.Contains x) : (reciprocal a h).Contains (1 / x) := by
  have hlo : (0 : ℝ) < a.lo := Rat.cast_pos.mpr h
  have hxp : 0 < x := hlo.trans_le hx.1
  constructor
  · simpa [reciprocal] using one_div_le_one_div_of_le hxp hx.2
  · simpa [reciprocal] using one_div_le_one_div_of_le hlo hx.1

/-- A proposed square-root interval is accepted by exact endpoint squares.
The square-root search algorithm is not part of the trusted computation. -/
def sqrtCheck (a proposed : Interval) : Bool :=
  decide (0 ≤ proposed.lo ∧ proposed.lo^2 ≤ a.lo ∧ a.hi ≤ proposed.hi^2)

theorem sqrtCheck_sound {a proposed : Interval} (h : sqrtCheck a proposed = true)
    {x : ℝ} (hx : a.Contains x) : proposed.Contains (Real.sqrt x) := by
  have hh : 0 ≤ proposed.lo ∧ proposed.lo^2 ≤ a.lo ∧ a.hi ≤ proposed.hi^2 :=
    of_decide_eq_true h
  have hlo : (0 : ℝ) ≤ proposed.lo := Rat.cast_nonneg.mpr hh.1
  have hhi : (0 : ℝ) ≤ proposed.hi := hlo.trans (Rat.cast_le.mpr proposed.ordered)
  have hslo : (proposed.lo : ℝ)^2 ≤ x := by
    exact (by exact_mod_cast hh.2.1 : (proposed.lo : ℝ)^2 ≤ a.lo).trans hx.1
  have hshi : x ≤ (proposed.hi : ℝ)^2 := by
    exact hx.2.trans (by exact_mod_cast hh.2.2)
  have hx0 : 0 ≤ x := (sq_nonneg (proposed.lo : ℝ)).trans hslo
  have hsq := Real.sq_sqrt hx0
  have hsr := Real.sqrt_nonneg x
  exact ⟨by nlinarith, Real.sqrt_le_iff.mpr ⟨hhi, hshi⟩⟩

end Interval
namespace Ball

def neg (a : Ball) : Ball := ⟨-a.center, a.radius, a.radius_nonneg⟩

theorem contains_neg {a : Ball} {x : ℝ} (ha : a.Contains x) : (neg a).Contains (-x) := by
  simpa only [Contains, neg, Rat.cast_neg, neg_sub_neg, abs_sub_comm] using ha

end Ball

structure ComplexRectangle where
  re : Ball
  im : Ball

namespace ComplexRectangle

def Contains (a : ComplexRectangle) (z : ℂ) : Prop := a.re.Contains z.re ∧ a.im.Contains z.im

def add (a b : ComplexRectangle) : ComplexRectangle := ⟨a.re.add b.re, a.im.add b.im⟩
def conjugate (a : ComplexRectangle) : ComplexRectangle := ⟨a.re, a.im.neg⟩
def mul (a b : ComplexRectangle) : ComplexRectangle :=
  ⟨(a.re.mul b.re).add ((a.im.mul b.im).neg),
   (a.re.mul b.im).add (a.im.mul b.re)⟩

theorem contains_add {a b : ComplexRectangle} {z w : ℂ}
    (hz : a.Contains z) (hw : b.Contains w) : (add a b).Contains (z + w) :=
  ⟨Ball.contains_add hz.1 hw.1, Ball.contains_add hz.2 hw.2⟩

theorem contains_conjugate {a : ComplexRectangle} {z : ℂ}
    (hz : a.Contains z) : (conjugate a).Contains (star z) :=
  ⟨hz.1, Ball.contains_neg hz.2⟩

theorem contains_mul {a b : ComplexRectangle} {z w : ℂ}
    (hz : a.Contains z) (hw : b.Contains w) : (mul a b).Contains (z * w) := by
  constructor
  · simpa only [Contains, mul, Complex.mul_re, sub_eq_add_neg] using
      Ball.contains_add (Ball.contains_mul hz.1 hw.1) (Ball.contains_neg (Ball.contains_mul hz.2 hw.2))
  · exact Ball.contains_add (Ball.contains_mul hz.1 hw.2) (Ball.contains_mul hz.2 hw.1)

end ComplexRectangle
end Maxwell.Certificate
