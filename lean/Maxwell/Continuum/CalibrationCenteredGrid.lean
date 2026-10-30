import Maxwell.Continuum.PeriodicCenteredLift
import Maxwell.Continuum.CalibrationGridPhase

/-! Executable rational centered representatives of the exact periodic
sampling grid. The half-period point is represented by positive one half. -/

namespace Maxwell.Continuum.Calibration

open PeriodicSampling Set

variable (N : ℕ) [NeZero N]

def centeredGrid (j : ZMod N) : ℚ :=
  if 2*j.val ≤ N then gridTurn N j else gridTurn N j-1

theorem centeredGrid_mem (j : ZMod N) :
    (centeredGrid N j : ℝ) ∈ Ioc (-(1/2) : ℝ) (1/2 : ℝ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hj : (j.val : ℝ) < N := by exact_mod_cast ZMod.val_lt j
  have hj0 : (0 : ℝ) ≤ j.val := by positivity
  unfold centeredGrid gridTurn
  split_ifs with h
  · push_cast
    have hb : 2*(j.val : ℝ) ≤ N := by exact_mod_cast h
    constructor
    · have hp : 0 ≤ (j.val : ℝ)/N := div_nonneg hj0 hn.le
      linarith
    · exact (div_le_iff₀ hn).mpr (by linarith)
  · push_cast
    have hb : (N : ℝ) < 2*(j.val : ℝ) := by exact_mod_cast Nat.lt_of_not_ge h
    constructor
    · have hp : (1/2 : ℝ) < (j.val : ℝ)/N := (lt_div_iff₀ hn).mpr (by linarith)
      linarith
    · have hp : (j.val : ℝ)/N < 1 := (div_lt_one hn).mpr hj
      linarith

omit [NeZero N] in
theorem centeredGrid_coe (j : ZMod N) :
    (((centeredGrid N j : ℚ) : ℝ) : UnitAddCircle) = (((j.val : ℝ)/N : ℝ) : UnitAddCircle) := by
  unfold centeredGrid gridTurn
  split_ifs
  · simp only [Rat.cast_div, Rat.cast_natCast]
  · simp only [Rat.cast_sub, Rat.cast_div, Rat.cast_natCast, Rat.cast_one,
      AddCircle.coe_sub, AddCircle.coe_period, sub_zero]

theorem centeredRepresentative_grid {ι : Type*} (j : ι → ZMod N) :
    centeredRepresentative (fun i => ((((j i).val : ℝ)/N : ℝ) : UnitAddCircle)) =
      fun i => (centeredGrid N (j i) : ℝ) := by
  have he : (fun i => ((((j i).val : ℝ)/N : ℝ) : UnitAddCircle)) =
      fun i => (((centeredGrid N (j i) : ℚ) : ℝ) : UnitAddCircle) := by
    funext i
    exact (centeredGrid_coe N (j i)).symm
  rw [he]
  exact centeredRepresentative_real _ (fun i => centeredGrid_mem N (j i))

#print axioms centeredRepresentative_grid

end Maxwell.Continuum.Calibration
