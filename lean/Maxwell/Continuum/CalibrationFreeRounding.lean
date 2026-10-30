import Maxwell.Continuum.CalibrationFreeProjection

/-! Uniform rounding bounds for the actual real free inverse. The
common momentum scale may vary in [3,4]; no alias radius occurs in
the estimate, because the longitudinal projection is unchanged. -/

namespace Maxwell.Continuum.Calibration

open FreeFiber

theorem free_denominator_lower {t E s : ℝ} (ht : 3 ≤ t) (hE : E ≤ 8) (hs : 2 ≤ s) :
    5*s ≤ t^2*s-E := by
  have ht2 : 9 ≤ t^2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right ht2 (by linarith : 0 ≤ s)
  nlinarith

theorem free_transverse_rounding {t u E F s : ℝ}
    (ht : 3 ≤ t ∧ t ≤ 4) (hu : 3 ≤ u ∧ u ≤ 4)
    (hE : E ≤ 8) (hF : F ≤ 8) (hs : 2 ≤ s) :
    |(t^2*s-E)⁻¹-(u^2*s-F)⁻¹| ≤ |t-u|+|E-F|/4 := by
  have hs0 : 0 < s := by linarith
  have hd := free_denominator_lower ht.1 hE hs
  have hd' := free_denominator_lower hu.1 hF hs
  have hd0 : 0 < t^2*s-E := by linarith
  have hd0' : 0 < u^2*s-F := by linarith
  have hn : |(u^2*s-F)-(t^2*s-E)| ≤ 8*s*|t-u|+|E-F| := by
    have he : (u^2*s-F)-(t^2*s-E) = (u-t)*(u+t)*s+(E-F) := by ring
    rw [he]
    calc
      _ ≤ |(u-t)*(u+t)*s|+|E-F| := abs_add_le _ _
      _ ≤ 8*s*|t-u|+|E-F| := by
        rw [abs_mul, abs_mul, abs_of_pos hs0, abs_of_nonneg (by linarith : 0 ≤ u+t), abs_sub_comm u t]
        have hmul := mul_le_mul_of_nonneg_right (show u+t ≤ 8 by linarith) (abs_nonneg (t-u))
        nlinarith
  rw [inv_sub_inv hd0.ne' hd0'.ne', abs_div, abs_mul, abs_of_pos hd0, abs_of_pos hd0']
  apply (div_le_iff₀ (mul_pos hd0 hd0')).mpr
  have hden : 25*s^2 ≤ (t^2*s-E)*(u^2*s-F) := by
    have h := mul_le_mul hd hd' (by positivity : 0 ≤ 5*s) hd0.le
    nlinarith
  have hab : 0 ≤ |t-u|+|E-F|/4 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hden hab
  have hS : 8*s ≤ 25*s^2 := by nlinarith
  have hS' : (4 : ℝ) ≤ 25*s^2 := by nlinarith
  have ha := mul_le_mul_of_nonneg_right hS (abs_nonneg (t-u))
  have hb := mul_le_mul_of_nonneg_right hS' (abs_nonneg (E-F))
  nlinarith

theorem free_longitudinal_rounding {E F : ℝ} (hE : 7 ≤ E) (hF : 7 ≤ F) :
    |E⁻¹-F⁻¹| ≤ |E-F|/2 := by
  have hE0 : 0 < E := by linarith
  have hF0 : 0 < F := by linarith
  rw [inv_sub_inv hE0.ne' hF0.ne', abs_div, abs_mul, abs_of_pos hE0, abs_of_pos hF0,
    abs_sub_comm F E]
  apply (div_le_iff₀ (mul_pos hE0 hF0)).mpr
  have hEF : 2 ≤ E*F := by nlinarith
  have h := mul_le_mul_of_nonneg_left hEF (abs_nonneg (E-F))
  nlinarith

theorem inverseBlock_real_scale_norm (t E : ℝ) (a : Fin 3 → ℝ)
    (ht : 3 ≤ t) (hE : 7 ≤ E ∧ E ≤ 8) (ha : 2 ≤ directionSquare a) :
    ‖inverseBlock (realMomentum (fun j => t*a j)) E‖ ≤ 1 := by
  have ha0 : 0 < directionSquare a := by linarith
  have hE0 : 0 < E := by linarith
  have hd := free_denominator_lower ht hE.2 ha
  have hd0 : 0 < t^2*directionSquare a-E := by linarith
  rw [inverseBlock_longitudinal t E a ha0.ne' hE0.ne' hd0.ne']
  calc
    _ ≤ ‖-((E : ℂ))⁻¹ • longitudinal a‖+
      ‖(((t^2*directionSquare a-E : ℝ) : ℂ))⁻¹ • ((1 : Polarization →L[ℂ] Polarization)-longitudinal a)‖ := norm_add_le _ _
    _ ≤ E⁻¹+2*(t^2*directionSquare a-E)⁻¹ := by
      simp only [norm_smul, norm_neg, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hE0, abs_of_pos hd0, longitudinal_norm a ha0, mul_one]
      have h := mul_le_mul_of_nonneg_left (transverse_norm a ha0) (inv_nonneg.mpr hd0.le)
      linarith
    _ ≤ 1 := by
      have hEi : E⁻¹ ≤ (7 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hE.1
      have hdi : (t^2*directionSquare a-E)⁻¹ ≤ (10 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by linarith)
      norm_num at hEi hdi
      linarith

theorem inverseBlock_real_scale_rounding (t u E F : ℝ) (a : Fin 3 → ℝ)
    (ht : 3 ≤ t ∧ t ≤ 4) (hu : 3 ≤ u ∧ u ≤ 4)
    (hE : 7 ≤ E ∧ E ≤ 8) (hF : 7 ≤ F ∧ F ≤ 8) (ha : 2 ≤ directionSquare a) :
    ‖inverseBlock (realMomentum (fun j => t*a j)) E-
      inverseBlock (realMomentum (fun j => u*a j)) F‖ ≤ 2*|t-u|+|E-F| := by
  have ha0 : 0 < directionSquare a := by linarith
  have hE0 : 0 < E := by linarith
  have hF0 : 0 < F := by linarith
  have hd0 : 0 < t^2*directionSquare a-E := by
    have := free_denominator_lower ht.1 hE.2 ha
    linarith
  have hd0' : 0 < u^2*directionSquare a-F := by
    have := free_denominator_lower hu.1 hF.2 ha
    linarith
  rw [inverseBlock_longitudinal t E a ha0.ne' hE0.ne' hd0.ne',
    inverseBlock_longitudinal u F a ha0.ne' hF0.ne' hd0'.ne']
  have heq : (-((E : ℂ))⁻¹) • longitudinal a+
      (((t^2*directionSquare a-E : ℝ) : ℂ))⁻¹ • ((1 : Polarization →L[ℂ] Polarization)-longitudinal a)-
      ((-((F : ℂ))⁻¹) • longitudinal a+
      (((u^2*directionSquare a-F : ℝ) : ℂ))⁻¹ • ((1 : Polarization →L[ℂ] Polarization)-longitudinal a)) =
      (((-(E⁻¹-F⁻¹) : ℝ) : ℂ)) • longitudinal a+
      ((((t^2*directionSquare a-E)⁻¹-(u^2*directionSquare a-F)⁻¹ : ℝ) : ℂ)) •
        ((1 : Polarization →L[ℂ] Polarization)-longitudinal a) := by push_cast; module
  rw [heq]
  calc
    _ ≤ ‖((((-(E⁻¹-F⁻¹) : ℝ) : ℂ))) • longitudinal a‖+
      ‖((((t^2*directionSquare a-E)⁻¹-(u^2*directionSquare a-F)⁻¹ : ℝ) : ℂ)) •
        ((1 : Polarization →L[ℂ] Polarization)-longitudinal a)‖ := norm_add_le _ _
    _ ≤ |E⁻¹-F⁻¹|+2*|(t^2*directionSquare a-E)⁻¹-(u^2*directionSquare a-F)⁻¹| := by
      simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_neg,
        longitudinal_norm a ha0, mul_one]
      have h := mul_le_mul_of_nonneg_left (transverse_norm a ha0)
        (abs_nonneg ((t^2*directionSquare a-E)⁻¹-(u^2*directionSquare a-F)⁻¹))
      linarith
    _ ≤ _ := by
      have h1 := free_longitudinal_rounding hE.1 hF.1
      have h2 := free_transverse_rounding ht hu hE.2 hF.2 ha
      linarith

#print axioms inverseBlock_real_scale_norm
#print axioms inverseBlock_real_scale_rounding

end Maxwell.Continuum.Calibration
