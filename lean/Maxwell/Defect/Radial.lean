import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The three-dimensional radial integral causing the square-root edge term. -/

open MeasureTheory Set Real

namespace Maxwell.Defect

theorem inverse_square_integrable_ball (R : ℝ) :
    IntegrableOn (fun q : EuclideanSpace ℝ (Fin 3) => 1 / ‖q‖ ^ 2)
      (Metric.ball 0 R) := by
  rw [integrableOn_fun_norm_addHaar volume (f := fun r : ℝ => 1 / r ^ 2)]
  apply (integrableOn_const (C := (1 : ℝ)) (s := Ioo 0 R)
    (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)).congr_fun
  · intro r hr
    have hr0 : r ≠ 0 := ne_of_gt hr.1
    simp [smul_eq_mul, hr0]
  · exact measurableSet_Ioo

/-- The singular error majorant is integrable in exactly the dimension
needed here, with an explicit finite coefficient. -/
theorem inverse_square_ball_integral {R : ℝ} (hR : 0 < R) :
    (∫ q : EuclideanSpace ℝ (Fin 3) in Metric.ball 0 R, 1 / ‖q‖ ^ 2) =
      4 * Real.pi * R := by
  rw [← integral_indicator measurableSet_ball]
  have hfun : (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R).indicator
      (fun q => 1 / ‖q‖ ^ 2) =
      fun q => (Iio R).indicator (fun r : ℝ => 1 / r ^ 2) ‖q‖ := by
    funext q
    simp [Set.indicator, Metric.mem_ball, dist_zero_right]
  rw [hfun, integral_fun_norm_addHaar volume]
  have hrad : (∫ r in Ioi (0 : ℝ),
      r ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1) •
        (Iio R).indicator (fun t : ℝ => 1 / t ^ 2) r) = R := by
    calc
      _ = ∫ r in Ioi (0 : ℝ), (Iio R).indicator (fun _ : ℝ => (1 : ℝ)) r := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        have hr0 : r ≠ 0 := ne_of_gt hr
        by_cases hrr : r < R <;> simp [Set.indicator, hrr, smul_eq_mul, hr0]
      _ = ∫ r in Ioo (0 : ℝ) R, (1 : ℝ) := by
        rw [setIntegral_indicator measurableSet_Iio]
        congr 1
      _ = R := by simp [Real.volume_real_Ioo, hR.le]
  rw [hrad]
  have hv : volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1) =
      Real.pi * 4 / 3 := by
    simp [Measure.real, EuclideanSpace.volume_ball_fin_three,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)]
  rw [hv]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul, nsmul_eq_mul]
  ring

theorem norm_integral_ball_error {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (error : EuclideanSpace ℝ (Fin 3) → F) {R C ξ : ℝ} (hR : 0 < R)
    (hbound : ∀ q ∈ Metric.ball 0 R, q ≠ 0 → ‖error q‖ ≤ C * ξ / ‖q‖ ^ 2) :
    ‖∫ q in Metric.ball 0 R, error q‖ ≤ 4 * Real.pi * R * C * ξ := by
  have hne : ∀ᵐ q : EuclideanSpace ℝ (Fin 3), q ≠ 0 := by simp [ae_iff]
  have hdom : IntegrableOn
      (fun q : EuclideanSpace ℝ (Fin 3) => C * ξ * (1 / ‖q‖ ^ 2))
      (Metric.ball 0 R) := (inverse_square_integrable_ball R).const_mul (C * ξ)
  have h := norm_integral_le_of_norm_le hdom (by
    filter_upwards [ae_restrict_mem measurableSet_ball, ae_restrict_of_ae hne] with q hq hq0
    simpa only [mul_one_div] using hbound q hq hq0)
  rw [integral_const_mul, inverse_square_ball_integral hR] at h
  convert h using 1; ring

theorem inverse_fourth_exterior_integral {R : ℝ} (hR : 0 < R) :
    (∫ q : EuclideanSpace ℝ (Fin 3) in (Metric.ball 0 R)ᶜ, 1 / ‖q‖ ^ 4) =
      4 * Real.pi / R := by
  rw [← integral_indicator measurableSet_ball.compl]
  have hfun : ((Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)ᶜ).indicator
      (fun q => 1 / ‖q‖ ^ 4) =
      fun q => (Ici R).indicator (fun r : ℝ => 1 / r ^ 4) ‖q‖ := by
    funext q
    simp [Set.indicator, Metric.mem_ball, dist_zero_right]
  rw [hfun, integral_fun_norm_addHaar volume]
  have hrad : (∫ r in Ioi (0 : ℝ),
      r ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1) •
        (Ici R).indicator (fun t : ℝ => 1 / t ^ 4) r) = 1 / R := by
    calc
      _ = ∫ r in Ioi (0 : ℝ), (Ici R).indicator (fun r : ℝ => 1 / r ^ 2) r := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        have hr0 : r ≠ 0 := ne_of_gt hr
        by_cases hrr : R ≤ r <;> simp [Set.indicator, hrr, smul_eq_mul]
        field_simp
      _ = ∫ r in Ici R, 1 / r ^ 2 := by
        rw [setIntegral_indicator measurableSet_Ici]
        have hs : Ioi (0 : ℝ) ∩ Ici R = Ici R :=
          inter_eq_right.mpr (fun _ hr => lt_of_lt_of_le hR hr)
        rw [hs]
      _ = ∫ r in Ioi R, r ^ (-2 : ℝ) := by
        rw [integral_Ici_eq_integral_Ioi]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        have hr0 : 0 ≤ r := (lt_trans hR hr).le
        dsimp
        rw [Real.rpow_neg hr0]
        norm_num [one_div]
      _ = 1 / R := by
        rw [integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) hR]
        norm_num [one_div, Real.rpow_neg hR.le]
  rw [hrad]
  have hv : volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1) =
      Real.pi * 4 / 3 := by
    simp [Measure.real, EuclideanSpace.volume_ball_fin_three,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)]
  rw [hv]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul, nsmul_eq_mul]
  ring

theorem inverse_fourth_integrable_exterior {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun q : EuclideanSpace ℝ (Fin 3) => 1 / ‖q‖ ^ 4)
      (Metric.ball 0 R)ᶜ := by
  apply Integrable.of_integral_ne_zero
  rw [inverse_fourth_exterior_integral hR]
  positivity

theorem norm_integral_exterior_error {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (error : EuclideanSpace ℝ (Fin 3) → F) {R C ξ : ℝ} (hR : 0 < R)
    (hbound : ∀ q ∈ (Metric.ball 0 R)ᶜ, ‖error q‖ ≤ C * ξ / ‖q‖ ^ 4) :
    ‖∫ q in (Metric.ball 0 R)ᶜ, error q‖ ≤ 4 * Real.pi / R * C * ξ := by
  have hdom : IntegrableOn
      (fun q : EuclideanSpace ℝ (Fin 3) => C * ξ * (1 / ‖q‖ ^ 4))
      (Metric.ball 0 R)ᶜ := (inverse_fourth_integrable_exterior hR).const_mul (C * ξ)
  have h := norm_integral_le_of_norm_le hdom (by
    filter_upwards [ae_restrict_mem measurableSet_ball.compl] with q hq
    simpa only [mul_one_div] using hbound q hq)
  rw [integral_const_mul, inverse_fourth_exterior_integral hR] at h
  convert h using 1; ring

theorem radial_resolvent_integral {ξ : ℝ} (hξ : 0 < ξ) :
    (∫ r in Ioi (0 : ℝ), ξ / (r ^ 2 + ξ)) = Real.sqrt ξ * Real.pi / 2 := by
  have hs : 0 < Real.sqrt ξ := Real.sqrt_pos.mpr hξ
  have hs2 : Real.sqrt ξ ^ 2 = ξ := Real.sq_sqrt hξ.le
  have hfun : (fun r : ℝ => ξ / (r ^ 2 + ξ)) =
      (fun r => (1 + ((Real.sqrt ξ)⁻¹ * r) ^ 2)⁻¹) := by
    funext r
    have hd : r ^ 2 + ξ ≠ 0 := ne_of_gt (by positivity)
    have hd' : 1 + ((Real.sqrt ξ)⁻¹ * r) ^ 2 ≠ 0 := ne_of_gt (by positivity)
    field_simp
    nlinarith
  rw [hfun, integral_comp_mul_left_Ioi (fun r : ℝ => (1 + r ^ 2)⁻¹) 0
    (inv_pos.mpr hs)]
  simp [integral_Ioi_inv_one_add_sq, smul_eq_mul]
  ring

theorem radial_three_dimensional_sqrt {ξ : ℝ} (hξ : 0 < ξ) :
    (∫ q : EuclideanSpace ℝ (Fin 3),
      ξ / (‖q‖ ^ 2 * (‖q‖ ^ 2 + ξ))) = 2 * Real.pi ^ 2 * Real.sqrt ξ := by
  rw [integral_fun_norm_addHaar volume (fun r : ℝ => ξ / (r ^ 2 * (r ^ 2 + ξ)))]
  have hr : (∫ r in Ioi (0 : ℝ),
      r ^ (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - 1) •
        (ξ / (r ^ 2 * (r ^ 2 + ξ)))) = Real.sqrt ξ * Real.pi / 2 := by
    rw [← radial_resolvent_integral hξ]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have hr0 : r ≠ 0 := ne_of_gt hr
    simp only [finrank_euclideanSpace, Fintype.card_fin, Nat.reduceSub, smul_eq_mul]
    field_simp
  rw [hr]
  have hv : volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1) =
      Real.pi * 4 / 3 := by
    simp [Measure.real, EuclideanSpace.volume_ball_fin_three,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi * 4 / 3)]
  rw [hv]
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul, nsmul_eq_mul]
  ring

/-- This is the isotropic coefficient with the paper's Bloch measure.
The anisotropic case additionally requires the determinant change of variables. -/
theorem normalized_radial_sqrt {ξ : ℝ} (hξ : 0 < ξ) :
    (∫ q : EuclideanSpace ℝ (Fin 3),
      ξ / (‖q‖ ^ 2 * (‖q‖ ^ 2 + ξ))) / (2 * Real.pi) ^ 3 =
      Real.sqrt ξ / (4 * Real.pi) := by
  rw [radial_three_dimensional_sqrt hξ]
  field_simp
  ring

/-- The determinant change of variables for any invertible linear square
root of a positive quadratic form. -/
theorem anisotropic_radial_sqrt
    (L : EuclideanSpace ℝ (Fin 3) ≃L[ℝ] EuclideanSpace ℝ (Fin 3))
    {ξ : ℝ} (hξ : 0 < ξ) :
    (∫ q : EuclideanSpace ℝ (Fin 3),
      ξ / (‖L q‖ ^ 2 * (‖L q‖ ^ 2 + ξ))) / (2 * Real.pi) ^ 3 =
      Real.sqrt ξ / (4 * Real.pi * |LinearMap.det L.toLinearEquiv.toLinearMap|) := by
  let f : EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun q => ξ / (‖q‖ ^ 2 * (‖q‖ ^ 2 + ξ))
  have hd : LinearMap.det L.toLinearEquiv.toLinearMap ≠ 0 :=
    L.toLinearEquiv.isUnit_det'.ne_zero
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) hd
  have hint := integral_map_equiv (μ := volume) L.toHomeomorph.toMeasurableEquiv f
  change (∫ q, f q ∂Measure.map L.toLinearEquiv.toLinearMap volume) =
    (∫ q, f (L q)) at hint
  rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)] at hint
  change (∫ q, f (L q)) / (2 * Real.pi) ^ 3 = _
  rw [← hint]
  change |(LinearMap.det L.toLinearEquiv.toLinearMap)⁻¹| *
    (∫ q, ξ / (‖q‖ ^ 2 * (‖q‖ ^ 2 + ξ))) / (2 * Real.pi) ^ 3 = _
  rw [radial_three_dimensional_sqrt hξ, abs_inv]
  field_simp
  ring

end Maxwell.Defect
