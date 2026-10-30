import Maxwell.Continuum.ProfileGlueEvaluation
import Maxwell.Continuum.CalibrationCenteredGrid

/-! Certified rational evaluation of the actual compact well root.
Rational samples use the exact squared Euclidean radius, including
points outside the support and arbitrarily close to its boundary. -/

namespace Maxwell.Continuum.Calibration

open Maxwell.Certificate Well

def rootArgument (y : Fin 3 → ℚ) : ℚ := 2*(1-∑ i, (y i)^2)

def rootApprox (y : Fin 3 → ℚ) (P : ℕ) : Ball := Profile.glueApprox (rootArgument y) P

theorem rootArgument_eq (y : Fin 3 → ℚ) :
    (rootArgument y : ℝ) = 2*(1-‖(WithLp.toLp 2 (fun i => (y i : ℝ)) : Space)‖^2) := by
  simp only [rootArgument, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_sub, Rat.cast_one,
    Rat.cast_sum, Rat.cast_pow, PiLp.norm_sq_eq_of_L2]
  congr 3
  funext i
  simp only [Real.norm_eq_abs, sq_abs]

theorem rootApprox_radius (y : Fin 3 → ℚ) (P : ℕ) :
    (rootApprox y P).radius = (1/2 : ℚ)^P := Profile.glueApprox_radius _ _

theorem rootApprox_contains (y : Fin 3 → ℚ) (P : ℕ) :
    (rootApprox y P).Contains (qw (WithLp.toLp 2 (fun i => (y i : ℝ)))) := by
  rw [qw_eq_glue, ← rootArgument_eq]
  exact Profile.glueApprox_contains _ _

theorem rootApprox_error (y : Fin 3 → ℚ) (P : ℕ) :
    |qw (WithLp.toLp 2 (fun i => (y i : ℝ)))-((rootApprox y P).center : ℝ)| ≤ (1/2 : ℝ)^P := by
  have h := rootApprox_contains y P
  rw [Ball.Contains, rootApprox_radius] at h
  simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h

#print axioms rootApprox_contains
#print axioms rootApprox_error

end Maxwell.Continuum.Calibration
