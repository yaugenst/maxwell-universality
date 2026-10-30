import Maxwell.Continuum.PeriodicPoleContourGeometry
import Maxwell.Continuum.PeriodicPoleDenominator

/-! The literal selected denominator on the growing rescaled cutoff
chart. Its lower bound is quadratic in real momentum; its complex-line
upper bound has the same order uniformly in the inverse length. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 8192

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric

attribute [local irreducible] dielectricBand imaginaryPole poleDenominator poleMomentum poleCenter

theorem dielectricBand_center_quadratic_bound {q : Momentum}
    (hq : ‖q‖ ≤ separatedRadius) :
    ‖dielectricBand q - dielectricBand 0‖ ≤ (2 : ℝ)^112 * ‖q‖^2 := by
  have hr := physical_quartic (hq.trans
    (by norm_num [separatedRadius, analyticRadius, backgroundAmplitude]))
  have hn : quarticConstant * separatedRadius^2 + (2 : ℝ)^110 ≤ (2 : ℝ)^112 := by
    norm_num [quarticConstant, analyticRadius, separatedRadius, backgroundAmplitude]
  calc
    _ ≤ ‖dielectricBand q - dielectricBand 0 - physicalQuadratic q‖ + ‖physicalQuadratic q‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        (dielectricBand q - dielectricBand 0 - physicalQuadratic q) (physicalQuadratic q)
    _ ≤ quarticConstant * ‖q‖^4 + (2 : ℝ)^110 * ‖q‖^2 :=
      add_le_add hr (physicalQuadratic_norm q)
    _ ≤ (quarticConstant * separatedRadius^2 + (2 : ℝ)^110) * ‖q‖^2 := by
      have hs := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hq 2)
        (mul_nonneg quarticConstant_nonneg (sq_nonneg ‖q‖))
      nlinarith only [hs]
    _ ≤ _ := mul_le_mul_of_nonneg_right hn (sq_nonneg _)

def globalPoleRadius (k : Space) : ℝ := 1 + ‖k‖

theorem globalPoleRadius_ge_one (k : Space) : 1 ≤ globalPoleRadius k := by
  unfold globalPoleRadius
  linarith only [norm_nonneg k]

theorem globalPoleRadius_pos (k : Space) : 0 < globalPoleRadius k :=
  zero_lt_one.trans_le (globalPoleRadius_ge_one k)

theorem globalPole_momentum_bound {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space)
    {v : Momentum} (hv : ‖v‖ ≤ 1) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 2*globalPoleRadius k) :
    ‖poleMomentum D hh j (realMomentum k.ofLp + ζ • v)‖ ≤ 3*h*globalPoleRadius k := by
  have hk := realMomentum_norm_le_euclidean k.ofLp
  have hz : ‖ζ • v‖ ≤ 2*globalPoleRadius k := by
    rw [norm_smul]
    exact (mul_le_mul hζ hv (norm_nonneg _)
      (mul_nonneg (by norm_num) (globalPoleRadius_pos k).le)).trans_eq (mul_one _)
  have ht := (norm_add_le (realMomentum k.ofLp) (ζ • v)).trans (add_le_add hk hz)
  apply (poleMomentum_norm_le D hh j _).trans
  have hm := mul_le_mul_of_nonneg_left ht D.h_pos.le
  unfold globalPoleRadius at hm ⊢
  nlinarith only [hm]

theorem globalPole_momentum_chart {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space)
    (hk : h*‖k‖ ≤ 4*smallRadius) {v : Momentum} (hv : ‖v‖ ≤ 1)
    {ζ : ℂ} (hζ : ‖ζ‖ ≤ 2*globalPoleRadius k) :
    ‖poleMomentum D hh j (realMomentum k.ofLp + ζ • v)‖ ≤ separatedRadius := by
  apply (globalPole_momentum_bound D hh j k hv hζ).trans
  have hn : 3*((1 / (2 : ℝ)^1024)+4*smallRadius) ≤ separatedRadius := by
    norm_num [smallRadius, separatedRadius, backgroundAmplitude]
  apply le_trans _ hn
  unfold globalPoleRadius
  nlinarith only [hk, hh]

theorem globalPole_line_analytic {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space)
    (hk : h*‖k‖ ≤ 4*smallRadius) {v : Momentum} (hv : ‖v‖ ≤ 1) :
    AnalyticOnNhd ℂ (fun ζ : ℂ => poleDenominator D hh j (realMomentum k.ofLp + ζ • v))
      (closedBall 0 (2*globalPoleRadius k)) := by
  intro ζ hζ
  have hζ' : ‖ζ‖ ≤ 2*globalPoleRadius k := by
    simpa only [mem_closedBall, dist_zero_right] using hζ
  have hq := globalPole_momentum_chart D hh j k hk hv hζ'
  have ha : AnalyticAt ℂ (fun w : ℂ => poleMomentum D hh j (realMomentum k.ofLp + w • v)) ζ := by
    unfold poleMomentum
    exact analyticAt_const.add ((analyticAt_const.add
      (analyticAt_id.smul analyticAt_const)).const_smul (c := (h : ℂ)))
  unfold poleDenominator
  apply analyticAt_const.mul
  apply AnalyticAt.sub _ analyticAt_const
  apply AnalyticAt.comp (f := fun w : ℂ => poleMomentum D hh j (realMomentum k.ofLp + w • v)) _ ha
  apply dielectricBand_analytic
  intro i
  exact (norm_le_pi_norm _ i).trans_lt (hq.trans_lt
    (by norm_num [separatedRadius, analyticRadius, backgroundAmplitude]))

theorem globalPole_line_norm_le {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space)
    (hk : h*‖k‖ ≤ 4*smallRadius) {v : Momentum} (hv : ‖v‖ ≤ 1)
    {ζ : ℂ} (hζ : ‖ζ‖ ≤ 2*globalPoleRadius k) :
    ‖poleDenominator D hh j (realMomentum k.ofLp + ζ • v)‖ ≤
      (2 : ℝ)^116 * (globalPoleRadius k)^2 := by
  let q := poleMomentum D hh j (realMomentum k.ofLp + ζ • v)
  have hq := globalPole_momentum_chart D hh j k hk hv hζ
  have hnq := globalPole_momentum_bound D hh j k hv hζ
  have hq0 : ‖poleCenter D hh j‖ ≤ separatedRadius := by
    rw [poleCenter_norm]
    exact (imaginaryPole_le_inverse_scale D hh j).trans
      (hh.trans (by norm_num [separatedRadius, backgroundAmplitude]))
  have hn0 : ‖poleCenter D hh j‖ ≤ h*globalPoleRadius k := by
    rw [poleCenter_norm]
    exact (imaginaryPole_le_inverse_scale D hh j).trans
      (by nlinarith only [globalPoleRadius_ge_one k, D.h_pos])
  have hroot : dielectricBand (poleCenter D hh j) = (z : ℂ) := by
    simpa only [poleCenter] using imaginaryPole_equation D hh j
  have hdiff : ‖dielectricBand q - (z : ℂ)‖ ≤
      (10*(2 : ℝ)^112) * (h*globalPoleRadius k)^2 := by
    rw [← hroot]
    have he : dielectricBand q - dielectricBand (poleCenter D hh j) =
        (dielectricBand q - dielectricBand 0) - (dielectricBand (poleCenter D hh j) - dielectricBand 0) := by ring
    rw [he]
    calc
      _ ≤ ‖dielectricBand q - dielectricBand 0‖ + ‖dielectricBand (poleCenter D hh j) - dielectricBand 0‖ := norm_sub_le _ _
      _ ≤ (2 : ℝ)^112*‖q‖^2 + (2 : ℝ)^112*‖poleCenter D hh j‖^2 :=
        add_le_add (dielectricBand_center_quadratic_bound hq) (dielectricBand_center_quadratic_bound hq0)
      _ ≤ (2 : ℝ)^112*(3*h*globalPoleRadius k)^2 + (2 : ℝ)^112*(h*globalPoleRadius k)^2 := by
        gcongr
      _ = _ := by ring
  unfold poleDenominator
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos D.h_pos]
  calc
    _ ≤ (h^2)⁻¹ * ((10*(2 : ℝ)^112) * (h*globalPoleRadius k)^2) :=
      mul_le_mul_of_nonneg_left hdiff (by positivity)
    _ = (10*(2 : ℝ)^112)*(globalPoleRadius k)^2 := by field_simp [D.h_pos.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg _)

theorem poleMomentum_real_shift {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space) :
    poleMomentum D hh j (realMomentum k.ofLp) =
      shiftedMomentum (h • k.ofLp) (axialPoleShift D hh j 1) := by
  funext i
  by_cases hij : i = j
  · subst i
    simp [poleMomentum, poleCenter, shiftedMomentum, realMomentum, axialPoleShift, basisVector]
    ring
  · simp [poleMomentum, poleCenter, shiftedMomentum, realMomentum, axialPoleShift, basisVector, hij]

theorem globalPole_denominator_lower {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space)
    (hk : h*‖k‖ ≤ 4*smallRadius) :
    ‖k‖^2 / 2 ≤ (poleDenominator D hh j (realMomentum k.ofLp)).re := by
  have hq : ‖realMomentum (h • k.ofLp)‖ ≤ 4*smallRadius := by
    have he : realMomentum (h • k.ofLp) = (h : ℂ) • realMomentum k.ofLp := by
      funext i
      simp [realMomentum]
    rw [he, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos D.h_pos]
    exact (mul_le_mul_of_nonneg_left (realMomentum_norm_le_euclidean k.ofLp) D.h_pos.le).trans hk
  have hc : ((h : ℂ)^2)⁻¹ = (((h^2)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [poleDenominator, hc, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, poleMomentum_real_shift]
  have hl := pole_path_denominator_lower D hh j
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by constructor <;> norm_num) (h • k.ofLp) hq
  have hm := mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr (sq_nonneg h))
  rw [hessianEnergy_smul] at hm
  have he : (h^2)⁻¹ * (h^2*hessianEnergy k.ofLp/2) = hessianEnergy k.ofLp/2 := by
    field_simp [D.h_pos.ne']
  rw [he] at hm
  exact (div_le_div_of_nonneg_right (euclidean_norm_sq_le_hessianEnergy k.ofLp)
    (by norm_num)).trans hm

theorem globalPole_denominator_norm_lower {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (k : Space)
    (hk : h*‖k‖ ≤ 4*smallRadius) :
    ‖k‖^2 / 2 ≤ ‖poleDenominator D hh j (realMomentum k.ofLp)‖ :=
  (globalPole_denominator_lower D hh j k hk).trans (Complex.re_le_norm _)

end Maxwell.Continuum.PeriodicBand
