import Maxwell.Continuum.CalibrationRationalFree
import Maxwell.Continuum.CalibrationCenteredGrid
import Maxwell.Continuum.CutoffProductEvaluation
import Maxwell.Continuum.AuxiliaryCutoff

/-! Arbitrary-precision rational cutoff evaluation at the actual finite
Bloch grid. The pi error is paid before normalization by the fixed
small momentum radius, and no support-boundary sign oracle is used. -/

namespace Maxwell.Continuum.Calibration

open Maxwell.Certificate Elementary PeriodicBand

def rationalSmallRadius : ℚ := (1/2)^140

theorem rationalSmallRadius_cast : (rationalSmallRadius : ℝ) = smallRadius := by
  norm_num [rationalSmallRadius, smallRadius, FreeFiber.backgroundAmplitude]

def normalizedGridArgument (r : Fin 3 → ℚ) (P : ℕ) : Fin 3 → ℚ :=
  fun j => piCenter (P+146)*r j/rationalSmallRadius

theorem normalizedGridArgument_error (r : Fin 3 → ℚ) (P : ℕ)
    (hr : ∀ j, |(r j : ℝ)| ≤ 1/2) (j : Fin 3) :
    |(Real.pi*(r j : ℝ))/smallRadius-(normalizedGridArgument r P j : ℝ)| ≤ (1/2 : ℝ)^(P+12) := by
  simp only [normalizedGridArgument, Rat.cast_div, Rat.cast_mul, rationalSmallRadius_cast,
    ← sub_div, ← sub_mul, abs_div, abs_mul, abs_of_pos smallRadius_pos]
  have hp := piCenter_error (P+146)
  calc
    _ ≤ ((1/2 : ℝ)^(P+146+6)*(1/2))/smallRadius := by
      exact div_le_div_of_nonneg_right (mul_le_mul hp (hr j) (abs_nonneg _)
        (by positivity)) smallRadius_pos.le
    _ ≤ (1/2 : ℝ)^(P+12) := by
      rw [← rationalSmallRadius_cast]
      simp only [rationalSmallRadius, Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
      simp only [pow_add]
      norm_num [div_eq_mul_inv]
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) P]

def gridCutoffApprox (r : Fin 3 → ℚ) (P : ℕ) : Ball :=
  chiApprox (normalizedGridArgument r P) P

theorem gridCutoffApprox_contains (r : Fin 3 → ℚ) (P : ℕ)
    (hr : ∀ j, |(r j : ℝ)| ≤ 1/2) :
    (gridCutoffApprox r P).Contains (Well.chi smallRadius (WithLp.toLp 2 (fun j => Real.pi*(r j : ℝ)))) :=
  chiApprox_contains _ _ _ _ (normalizedGridArgument_error r P hr)

theorem gridCutoffApprox_error (r : Fin 3 → ℚ) (P : ℕ)
    (hr : ∀ j, |(r j : ℝ)| ≤ 1/2) :
    |Well.chi smallRadius (WithLp.toLp 2 (fun j => Real.pi*(r j : ℝ)))-(gridCutoffApprox r P).center| ≤ (1/2 : ℝ)^P := by
  have h := gridCutoffApprox_contains r P hr
  change |Well.chi smallRadius (WithLp.toLp 2 (fun j => Real.pi*(r j : ℝ)))-(gridCutoffApprox r P).center| ≤
    ((chiApprox (normalizedGridArgument r P) P).radius : ℝ) at h
  simpa only [chiApprox, Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h

#print axioms gridCutoffApprox_contains

end Maxwell.Continuum.Calibration
