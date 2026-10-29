import Maxwell.Continuum.PeriodicTubeShift

/-! A fixed bound on the full inverse in the cutoff transition shell.
The imaginary displacement is allowed twice the energy-scale radius,
so this estimate also reaches the eventual limiting pole contour. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary

attribute [local irreducible] dielectricBand hessianEnergy shiftedMomentum
  CellGauge.fullCellSymbol fullFiberResolvent

theorem hessianEnergy_euclidean_lower (q : Corner.Vec) :
    (2 * backgroundAmplitude)⁻¹ * ‖(WithLp.toLp 2 q : Space)‖^2 ≤ hessianEnergy q := by
  have he : ‖(WithLp.toLp 2 q : Space)‖^2 = dotProduct q q := by
    simpa only [dotProduct, pow_two] using
      EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 q : Space)
  rw [he]
  simpa only [hessianEnergy] using (hessian_bounds q).1

theorem realMomentum_norm_le_euclidean (q : Corner.Vec) :
    ‖realMomentum q‖ ≤ ‖(WithLp.toLp 2 q : Space)‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro j
  simpa only [realMomentum, Complex.norm_real] using
    PiLp.norm_apply_le (WithLp.toLp 2 q : Space) j

theorem transition_energy_lower (q : Corner.Vec)
    (hq : smallRadius ≤ ‖(WithLp.toLp 2 q : Space)‖) :
    1 / (2 : ℝ)^181 ≤ hessianEnergy q := by
  have he := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ smallRadius_pos.le hq 2)
    (show (0 : ℝ) ≤ (2 * backgroundAmplitude)⁻¹ from
      inv_nonneg.mpr (mul_nonneg (by norm_num) backgroundAmplitude_pos.le))
  have hn : (2 * backgroundAmplitude)⁻¹ * smallRadius^2 = 1 / (2 : ℝ)^181 := by
    norm_num [backgroundAmplitude, smallRadius]
  rw [hn] at he
  exact he.trans (hessianEnergy_euclidean_lower q)

theorem wide_tube_shift_norm_le {h : ℝ} (h0 : 0 ≤ h) (b : Corner.Vec)
    (hb : hessianEnergy b ≤ 4 * h^2) : ‖realMomentum b‖ ≤ 2 * h := by
  have he := (norm_sq_le_hessianEnergy b).trans hb
  nlinarith [norm_nonneg (realMomentum b)]

theorem wide_tube_chart_radius {h : ℝ} (h0 : 0 ≤ h)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (q b : Corner.Vec)
    (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) (hb : hessianEnergy b ≤ 4 * h^2) :
    ‖shiftedMomentum q b‖ ≤ separatedRadius := by
  calc
    _ ≤ ‖realMomentum q‖ + ‖realMomentum b‖ := shiftedMomentum_norm_le q b
    _ ≤ 4 * smallRadius + 2 * (1 / (2 : ℝ)^1024) :=
      add_le_add hq ((wide_tube_shift_norm_le h0 b hb).trans
        (mul_le_mul_of_nonneg_left hh (by norm_num)))
    _ ≤ _ := by norm_num [smallRadius, separatedRadius, backgroundAmplitude]

theorem wide_tube_remainder_norm {h : ℝ} (h0 : 0 ≤ h)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (q b : Corner.Vec)
    (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) (hb : hessianEnergy b ≤ 4 * h^2) :
    ‖dielectricBand (shiftedMomentum q b) - dielectricBand 0 -
      physicalQuadratic (shiftedMomentum q b)‖ ≤ hessianEnergy q / 1000 + 2 * h^2 := by
  have hc := quarticConstant_nonneg
  have hn := wide_tube_shift_norm_le h0 b hb
  have hs := (imaginary_scale_bounds h0 hh).2.1
  have him : 8 * quarticConstant * ‖realMomentum b‖^4 ≤ 2 * h^2 := by
    have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg (2 * h))
    have hbound : 8 * quarticConstant * (2 * h)^4 ≤ 2 * h^2 := by nlinarith
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hn 4)
      (by positivity : 0 ≤ 8 * quarticConstant)).trans hbound
  have hr : ‖shiftedMomentum q b‖ ≤ analyticRadius / 2 :=
    (wide_tube_chart_radius h0 hh q b hq hb).trans
      (by norm_num [separatedRadius, analyticRadius, backgroundAmplitude])
  calc
    _ ≤ quarticConstant * ‖shiftedMomentum q b‖^4 := physical_quartic hr
    _ ≤ quarticConstant * (8 * (‖realMomentum q‖^4 + ‖realMomentum b‖^4)) :=
      mul_le_mul_of_nonneg_left (shiftedMomentum_norm_fourth q b) hc
    _ = 8 * quarticConstant * ‖realMomentum q‖^4 +
        8 * quarticConstant * ‖realMomentum b‖^4 := by ring
    _ ≤ _ := add_le_add (tube_real_quartic q hq) him

theorem transition_denominator_lower {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ : σ ≤ h^4 / 64)
    (q b : Corner.Vec) (hq0 : smallRadius ≤ ‖(WithLp.toLp 2 q : Space)‖)
    (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) (hb : hessianEnergy b ≤ 4 * h^2) :
    hessianEnergy q / 2 ≤
      (dielectricBand (shiftedMomentum q b) - ((z + σ : ℝ) : ℂ)).re := by
  have he := (Complex.abs_re_le_norm _).trans (wide_tube_remainder_norm D.h_pos.le hh q b hq hb)
  simp only [Complex.sub_re, shifted_quadratic_re] at he
  change |(dielectricBand (shiftedMomentum q b)).re - centerEnergy -
    (hessianEnergy q - hessianEnergy b)| ≤ hessianEnergy q / 1000 + 2 * h^2 at he
  have h2 := pow_le_pow_left₀ D.h_pos.le hh 2
  have htiny : 16 * h^2 ≤ hessianEnergy q := by
    calc
      _ ≤ 16 * (1 / (2 : ℝ)^1024)^2 := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ ≤ 1 / (2 : ℝ)^181 := by norm_num
      _ ≤ _ := transition_energy_lower q hq0
  have hsq : h^2 ≤ 1 := h2.trans (by norm_num)
  have h4 : h^4 ≤ h^2 := by nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg h)]
  have hz := (abs_le.mp D.error).2
  have hl := (abs_le.mp he).1
  simp only [Complex.sub_re, Complex.ofReal_re]
  nlinarith [sq_nonneg h]

theorem transition_denominator_ne_zero {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ : σ ≤ h^4 / 64)
    (q b : Corner.Vec) (hq0 : smallRadius ≤ ‖(WithLp.toLp 2 q : Space)‖)
    (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) (hb : hessianEnergy b ≤ 4 * h^2) :
    dielectricBand (shiftedMomentum q b) - ((z + σ : ℝ) : ℂ) ≠ 0 := by
  intro he
  have hl := transition_denominator_lower D hh hσ q b hq0 hq hb
  rw [he, Complex.zero_re] at hl
  have hp := transition_energy_lower q hq0
  have : (0 : ℝ) < 1 / 2^181 := by positivity
  linarith

theorem transition_inverse_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ : σ ≤ h^4 / 64)
    (q b : Corner.Vec) (hq0 : smallRadius ≤ ‖(WithLp.toLp 2 q : Space)‖)
    (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) (hb : hessianEnergy b ≤ 4 * h^2) :
    ‖(dielectricBand (shiftedMomentum q b) - ((z + σ : ℝ) : ℂ))⁻¹‖ ≤ (2 : ℝ)^182 := by
  have hl : 1 / (2 : ℝ)^182 ≤
      ‖dielectricBand (shiftedMomentum q b) - ((z + σ : ℝ) : ℂ)‖ := by
    calc
      _ = (1 / (2 : ℝ)^181) / 2 := by norm_num
      _ ≤ hessianEnergy q / 2 := div_le_div_of_nonneg_right (transition_energy_lower q hq0) (by norm_num)
      _ ≤ (dielectricBand (shiftedMomentum q b) - ((z + σ : ℝ) : ℂ)).re :=
        transition_denominator_lower D hh hσ q b hq0 hq hb
      _ ≤ _ := Complex.re_le_norm _
  rw [norm_inv]
  exact (inv_anti₀ (by positivity : (0 : ℝ) < 1 / 2^182) hl).trans_eq (by norm_num)

theorem transition_fiber_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (q b : Corner.Vec) (hq0 : smallRadius ≤ ‖(WithLp.toLp 2 q : Space)‖)
    (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) (hb : hessianEnergy b ≤ 4 * h^2) :
    ‖fullFiberResolvent z σ (shiftedMomentum q b)‖ ≤ (2 : ℝ)^192 := by
  have hp := fullFiberResolvent_norm_le_pole D hσ0 hσ
    (wide_tube_chart_radius D.h_pos.le hh q b hq hb)
    (transition_denominator_ne_zero D hh hσ q b hq0 hq hb)
  calc
    _ ≤ ‖(dielectricBand (shiftedMomentum q b) - ((z + σ : ℝ) : ℂ))⁻¹‖ *
        (81 / 25) + (2 : ℝ)^112 := hp
    _ ≤ (2 : ℝ)^182 * (81 / 25) + (2 : ℝ)^112 := by
      gcongr
      exact transition_inverse_norm_le D hh hσ q b hq0 hq hb
    _ ≤ _ := by norm_num

theorem transition_cell_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (q b : Corner.Vec) (hq0 : smallRadius ≤ ‖(WithLp.toLp 2 q : Space)‖)
    (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) (hb : hessianEnergy b ≤ 4 * h^2) :
    ‖CellGauge.fullCellSymbol z σ (shiftedMomentum q b)‖ ≤ (2 : ℝ)^196 := by
  have hg := CellGauge.cellGauge_small_bound (wide_tube_chart_radius D.h_pos.le hh q b hq hb)
  have hf := (CellGauge.conjugate_bound (fullFiberResolvent z σ (shiftedMomentum q b))).trans
    (transition_fiber_norm_le D hh hσ0 hσ q b hq0 hq hb)
  unfold CellGauge.fullCellSymbol
  calc
    _ ≤ ‖CellGauge.antiGauge (shiftedMomentum q b)‖ *
        ‖(CellGauge.conjugate (fullFiberResolvent z σ (shiftedMomentum q b))).comp
          (CellGauge.antiUngauge (shiftedMomentum q b))‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 3 * ((2 : ℝ)^192 * 3) := by
      apply mul_le_mul hg.1 _ (norm_nonneg _) (by norm_num)
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul hf hg.2 (norm_nonneg _) (by positivity))
    _ ≤ _ := by norm_num

theorem transition_cell_analyticAt {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    (q b : Corner.Vec) (hq0 : smallRadius ≤ ‖(WithLp.toLp 2 q : Space)‖)
    (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) (hb : hessianEnergy b ≤ 4 * h^2) :
    AnalyticAt ℂ (CellGauge.fullCellSymbol z σ) (shiftedMomentum q b) :=
  CellGauge.fullCellSymbol_analyticAt D hσ0 hσ
    (wide_tube_chart_radius D.h_pos.le hh q b hq hb)
    (transition_denominator_ne_zero D hh hσ q b hq0 hq hb)

end Maxwell.Continuum.PeriodicBand
