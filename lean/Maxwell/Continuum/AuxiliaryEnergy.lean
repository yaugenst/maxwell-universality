import Maxwell.Continuum.PeriodicPhysicalCurvature

/-! Physical energy inclusion for the continuum cutoff inverse. The only
energy input is the stated calibration error; the selected denominator
and the local resolvent window are derived from the actual band. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Auxiliary

open FreeFiber PeriodicBand

def centerEnergy : ℝ := (dielectricBand 0).re

/-- A calibrated real energy at inverse length `h`. The mild upper bound
on `h` is far weaker than the paper's symbolic minimum length. -/
structure Calibration (h z : ℝ) : Prop where
  h_pos : 0 < h
  h_le : h ≤ backgroundAmplitude
  error : |z - (centerEnergy - h ^ 2)| ≤ h ^ 4

theorem dot_le_small_support (q : Corner.Vec)
    (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) :
    dotProduct q q ≤ 3 * (4 * smallRadius) ^ 2 := by
  have hc (j : Fin 3) : |q j| ≤ 4 * smallRadius := by
    have h := (norm_le_pi_norm (realMomentum q) j).trans hq
    simpa only [realMomentum, Complex.norm_real, Real.norm_eq_abs] using h
  have hsq (j : Fin 3) : q j ^ 2 ≤ (4 * smallRadius) ^ 2 := by
    nlinarith [sq_nonneg (4 * smallRadius - |q j|), sq_abs (q j),
      abs_nonneg (q j), smallRadius_pos, hc j]
  simp only [dotProduct, Fin.sum_univ_three]
  nlinarith [hsq 0, hsq 1, hsq 2]

theorem band_rise_bounds (q : Corner.Vec)
    (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) :
    0 ≤ (dielectricBand (realMomentum q)).re - centerEnergy ∧
      (dielectricBand (realMomentum q)).re - centerEnergy ≤ backgroundAmplitude / 1000 := by
  have hc := physical_small_curvature q hq
  have hρ := backgroundAmplitude_pos
  have hh := hessian_bounds q
  have hd := dot_le_small_support q hq
  have hlo : 0 ≤ dotProduct q (hessian.mulVec q) :=
    le_trans (mul_nonneg (inv_nonneg.mpr (by positivity)) (dot_self_nonneg q)) hh.1
  constructor
  · change 0 ≤ (dielectricBand (realMomentum q)).re - (dielectricBand 0).re
    linarith
  · have hbound : (3 / 2 : ℝ) * (256 / backgroundAmplitude) *
        (3 * (4 * smallRadius)^2) ≤ backgroundAmplitude / 1000 := by
      norm_num [backgroundAmplitude, smallRadius]
    have hmul := mul_le_mul_of_nonneg_left hd
      (show 0 ≤ (256 / backgroundAmplitude : ℝ) by positivity)
    change (dielectricBand (realMomentum q)).re - (dielectricBand 0).re ≤ _
    nlinarith

theorem amplitude_small : backgroundAmplitude ≤ 1 / 4 := by
  norm_num [backgroundAmplitude]

theorem calibration_h_small {h z : ℝ} (D : Calibration h z) : h ≤ 1 / 4 :=
  D.h_le.trans amplitude_small

theorem calibration_denominator_bounds {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) :
    h ^ 2 / 2 ≤ (dielectricBand (realMomentum q)).re - (z + σ) ∧
      (dielectricBand (realMomentum q)).re - (z + σ) ≤ backgroundAmplitude / 200 := by
  have hb := band_rise_bounds q hq
  have he := abs_le.mp D.error
  have hh := calibration_h_small D
  have h2 : h ^ 2 ≤ (1 / 4 : ℝ)^2 := by nlinarith [D.h_pos]
  have h4 : h ^ 4 ≤ h ^ 2 / 16 := by
    nlinarith [mul_le_mul_of_nonneg_right h2 (sq_nonneg h)]
  constructor
  · nlinarith [sq_nonneg h]
  · have hρ2 : h ^ 2 ≤ backgroundAmplitude ^ 2 := by
      nlinarith [D.h_pos, D.h_le, backgroundAmplitude_pos]
    have hconst : backgroundAmplitude / 1000 +
        (17 / 16 : ℝ) * backgroundAmplitude ^ 2 ≤ backgroundAmplitude / 200 := by
      norm_num [backgroundAmplitude]
    nlinarith

end Maxwell.Continuum.Auxiliary
