import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Explicit stability of the positive inverse square root. -/

namespace Maxwell.Continuum

theorem inv_sqrt_sub_abs {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |(Real.sqrt a)⁻¹ - (Real.sqrt b)⁻¹| =
      |a - b| / (Real.sqrt a * Real.sqrt b * (Real.sqrt a + Real.sqrt b)) := by
  have ha' := Real.sqrt_pos.mpr ha
  have hb' := Real.sqrt_pos.mpr hb
  have hs : Real.sqrt a + Real.sqrt b ≠ 0 := by positivity
  have hid : b - a = (Real.sqrt b - Real.sqrt a) * (Real.sqrt a + Real.sqrt b) := by
    nlinarith [Real.sq_sqrt ha.le, Real.sq_sqrt hb.le]
  have heq : (Real.sqrt a)⁻¹ - (Real.sqrt b)⁻¹ =
      (b - a) / (Real.sqrt a * Real.sqrt b * (Real.sqrt a + Real.sqrt b)) := by
    rw [hid]
    field_simp
  rw [heq, abs_div, abs_sub_comm]
  rw [abs_of_pos (show 0 < Real.sqrt a * Real.sqrt b * (Real.sqrt a + Real.sqrt b) by
    positivity)]

theorem inv_sqrt_sub_bound {a b : ℝ} (hb : 0 < b) (hab : b / 2 ≤ a) :
    |(Real.sqrt a)⁻¹ - (Real.sqrt b)⁻¹| ≤
      2 * |a - b| / (b * Real.sqrt b) := by
  have ha : 0 < a := by linarith
  have ha' := Real.sqrt_pos.mpr ha
  have hb' := Real.sqrt_pos.mpr hb
  have hhalf : Real.sqrt b / 2 ≤ Real.sqrt a := by
    nlinarith [Real.sq_sqrt ha.le, Real.sq_sqrt hb.le]
  have hprod : (b * Real.sqrt b) / 2 ≤
      Real.sqrt a * Real.sqrt b * (Real.sqrt a + Real.sqrt b) := by
    calc
      _ = (Real.sqrt b / 2) * Real.sqrt b * Real.sqrt b := by
        nlinarith [Real.sq_sqrt hb.le]
      _ ≤ (Real.sqrt a * Real.sqrt b) * (Real.sqrt a + Real.sqrt b) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hhalf hb'.le) (by linarith)
          hb'.le (mul_nonneg ha'.le hb'.le)
  rw [inv_sqrt_sub_abs ha hb]
  calc
    _ ≤ |a - b| / ((b * Real.sqrt b) / 2) :=
      div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hprod
    _ = 2 * |a - b| / (b * Real.sqrt b) := by ring

end Maxwell.Continuum
