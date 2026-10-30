import Maxwell.Certificate.Interval

/-! Rational interval outputs for certified continuum calibration.
The record contains rational data; containment is a separate proved
semantic relation to the actual continuum quantity. -/

namespace Maxwell.Certificate.Interval

def width (I : Interval) : ℚ := I.hi-I.lo

def midpoint (I : Interval) : ℚ := (I.lo+I.hi)/2

theorem width_nonneg (I : Interval) : 0 ≤ I.width := sub_nonneg.mpr I.ordered

theorem midpoint_error (I : Interval) {x : ℝ} (hx : I.Contains x) :
    |(I.midpoint : ℝ)-x| ≤ (I.width : ℝ)/2 := by
  obtain ⟨hl, hu⟩ := hx
  simp only [midpoint, width, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat, Rat.cast_sub]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem midpoint_error_of_width (I : Interval) {x : ℝ} (hx : I.Contains x)
    {ε : ℚ} (hε : I.width ≤ 2*ε) : |(I.midpoint : ℝ)-x| ≤ (ε : ℝ) := by
  have hw : (I.width : ℝ) ≤ 2*(ε : ℝ) := by exact_mod_cast hε
  exact (I.midpoint_error hx).trans (by linarith)

end Maxwell.Certificate.Interval

namespace Maxwell.Continuum.Calibration

/-- Continuum calibration uses the common verified rational interval type. -/
abbrev RationalInterval := Maxwell.Certificate.Interval

end Maxwell.Continuum.Calibration
