import Maxwell.Continuum.AxialSourceCoupling
import Maxwell.Continuum.CellSourceScaledIntegral

/-! The physical nearest-neighbor coupling equals the rescaled scalar
pole integral plus the proved exponentially small contour error. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096
set_option maxRecDepth 2048

namespace Maxwell.Continuum.CellGauge

open Complex FreeFiber PeriodicBand EffectiveMass Auxiliary AlmostAnalytic MasterConstants MeasureTheory

attribute [local irreducible] realMode fullCellSymbol

theorem cellSource_prefactor_norm_le : ‖((64*blochDensity : ℝ) : ℂ)‖ ≤ 64 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) blochDensity_pos)]
  exact (mul_le_mul_of_nonneg_left blochDensity_le_one (by norm_num)).trans_eq (mul_one _)

theorem axialSourceCoupling_contour_error {L : ℕ} {z : ℝ} (hL : Ls ≤ (L : ℝ))
    (hLe : Even L) (D : Calibration (L : ℝ)⁻¹ z) (j : Fin 3) (d : ℕ) :
    ‖axialSourceCoupling D (inverse_length_le_1024 hL) j (d : ℝ)-
      ((64*blochDensity : ℝ) : ℂ)*∫ q,
        sourcePoleContourIntegrand D (inverse_length_le_1024 hL) j
          (realMode D (inverse_length_le_1024 hL)) (realMode D (inverse_length_le_1024 hL))
          (poleAxialDisplacement (L : ℝ)⁻¹ (d : ℝ) j) 1 q‖ ≤
      (2 : ℝ)^341*(L : ℝ)^3*Real.exp (-cs*(L : ℝ)) := by
  let hh := inverse_length_le_1024 hL
  rw [axialSourceCoupling_fourier hL hLe, ← mul_sub, norm_mul]
  have he := sourcePoleContour_endpoint_error hL D j (realMode_norm D hh).le (realMode_norm D hh).le
    (poleAxialDisplacement (L : ℝ)⁻¹ (d : ℝ) j)
    (poleContourShift_axial_phase_nonneg D hh j (Nat.cast_nonneg d))
  rw [norm_sub_rev] at he
  apply (mul_le_mul cellSource_prefactor_norm_le he (norm_nonneg _) (by norm_num)).trans_eq
  rw [show (341 : ℕ) = 6+335 by omega, pow_add]
  ring

theorem sourcePoleContour_length_scaled {L z : ℝ} (hL : Ls ≤ L)
    (D : Calibration L⁻¹ z) (j : Fin 3) (d : ℝ) :
    ((64*blochDensity : ℝ) : ℂ)*(∫ q, sourcePoleContourIntegrand D (inverse_length_le_1024 hL) j
      (realMode D (inverse_length_le_1024 hL)) (realMode D (inverse_length_le_1024 hL))
      (poleAxialDisplacement L⁻¹ d j) 1 q) =
      ((L^2*Real.exp (-poleAction D (inverse_length_le_1024 hL) j*d) : ℝ) : ℂ)*
        OperatorFourier.angularFourier
          (fun k => cutoffSelectedQuotient D (inverse_length_le_1024 hL) j k+
            separatedRegularSymbol D (inverse_length_le_1024 hL) j
              (realMode D (inverse_length_le_1024 hL)) (realMode D (inverse_length_le_1024 hL)) k)
          (-(2*(placementDiagonal j : ℝ)*d) • PiLp.single 2 j 1) := by
  let hh := inverse_length_le_1024 hL
  have he := sourcePoleContour_scaled_integral D hh j d
  have hL0 : L ≠ 0 := (length_pos hL).ne'
  have hm := congrArg (fun x : ℂ => (L : ℂ)^2*x) he
  simp only [Complex.ofReal_inv] at hm
  have hc (C J : ℂ) : (L : ℂ)^2*((L : ℂ)⁻¹^2*C*J) = C*J := by
    field_simp [Complex.ofReal_ne_zero.mpr hL0]
  rw [hc] at hm
  convert hm using 1
  push_cast
  ring

theorem axialSourceCoupling_scaled_error {L : ℕ} {z : ℝ} (hL : Ls ≤ (L : ℝ))
    (hLe : Even L) (D : Calibration (L : ℝ)⁻¹ z) (j : Fin 3) (d : ℕ) :
    ‖axialSourceCoupling D (inverse_length_le_1024 hL) j (d : ℝ)-
      (((L : ℝ)^2*Real.exp (-poleAction D (inverse_length_le_1024 hL) j*(d : ℝ)) : ℝ) : ℂ)*
        OperatorFourier.angularFourier
          (fun k => cutoffSelectedQuotient D (inverse_length_le_1024 hL) j k+
            separatedRegularSymbol D (inverse_length_le_1024 hL) j
              (realMode D (inverse_length_le_1024 hL)) (realMode D (inverse_length_le_1024 hL)) k)
          (-(2*(placementDiagonal j : ℝ)*(d : ℝ)) • PiLp.single 2 j 1)‖ ≤
      (2 : ℝ)^341*(L : ℝ)^3*Real.exp (-cs*(L : ℝ)) := by
  rw [← sourcePoleContour_length_scaled hL D j (d : ℝ)]
  exact axialSourceCoupling_contour_error hL hLe D j d

#print axioms axialSourceCoupling_scaled_error

end Maxwell.Continuum.CellGauge
