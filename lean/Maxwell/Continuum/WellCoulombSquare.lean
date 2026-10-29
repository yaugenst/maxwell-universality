import Maxwell.Continuum.WellKernelConstants
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! The inverse-square singularity is locally integrable in the actual
three-dimensional Euclidean measure, with its exact radial integral. -/

noncomputable section

namespace Maxwell.Continuum.Well

open MeasureTheory Set Metric

theorem inverseSquare_integrable_ball (R : ℝ) :
    IntegrableOn (fun x : Space => (‖x‖ ^ 2)⁻¹) (ball 0 R) := by
  apply (integrableOn_fun_norm_addHaar (volume : Measure Space)
    (f := fun r : ℝ => (r ^ 2)⁻¹)).mpr
  have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo 0 R) :=
    integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  apply hc.congr_fun _ measurableSet_Ioo
  intro r hr
  simp only [Space, finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul]
  exact (mul_inv_cancel₀ (pow_ne_zero _ hr.1.ne')).symm

theorem inverseSquare_integral_ball (R : ℝ) (hR : 0 ≤ R) :
    (∫ x : Space in ball 0 R, (‖x‖ ^ 2)⁻¹) = 4 * Real.pi * R := by
  let f : ℝ → ℝ := (Iio R).indicator (fun r => (r ^ 2)⁻¹)
  have hcomp : (fun x : Space => f ‖x‖) =
      (ball (0 : Space) R).indicator (fun x => (‖x‖ ^ 2)⁻¹) := by
    funext x
    simp [f, indicator]
  have hr : (∫ r : ℝ in Ioi 0, r ^ 2 * f r) = R := by
    calc
      _ = ∫ r : ℝ in Ioi 0, (Iio R).indicator (fun _ => (1 : ℝ)) r := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        by_cases h : r < R
        · simp [f, h, pow_ne_zero 2 hr.out.ne']
        · simp [f, h]
      _ = ∫ r : ℝ in Ioo 0 R, (1 : ℝ) := by
        rw [setIntegral_indicator measurableSet_Iio]
        rfl
      _ = R := by
        rw [setIntegral_const, measureReal_def, Real.volume_Ioo,
          ENNReal.toReal_ofReal (by simpa using hR)]
        simp
  have h := integral_fun_norm_addHaar (volume : Measure Space) f
  rw [hcomp, integral_indicator measurableSet_ball] at h
  simp only [Space, finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub,
    smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat] at h
  rw [hr] at h
  rw [h, measureReal_def, EuclideanSpace.volume_ball_fin_three]
  norm_num only [ENNReal.ofReal_one, one_pow, one_mul,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)]
  ring

theorem inverseSquare_integral_ball_two :
    (∫ x : Space in ball 0 2, (‖x‖ ^ 2)⁻¹) ≤ 32 := by
  rw [inverseSquare_integral_ball 2 (by norm_num)]
  linarith [Real.pi_lt_four]

end Maxwell.Continuum.Well
