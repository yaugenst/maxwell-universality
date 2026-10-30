import Maxwell.Continuum.FullCellPairing
import Maxwell.Continuum.PeriodicTubeShift

/-! Literal complex Cauchy discs for the complete continuum cell inverse.
Their width is proportional to the inverse physical length. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.CellGauge

open FreeFiber Auxiliary PeriodicBand Set Metric

attribute [local irreducible] fullCellSymbol

def fullCellRadius (h : ℝ) : ℝ := h / (2 : ℝ)^256

theorem fullCellRadius_pos {h : ℝ} (hh : 0 < h) : 0 < fullCellRadius h :=
  div_pos hh (by positivity)

theorem fullCellRadius_le_small {h z : ℝ} (D : Calibration h z) :
    fullCellRadius h ≤ smallRadius := by
  calc
    _ ≤ backgroundAmplitude / (2 : ℝ)^256 :=
      div_le_div_of_nonneg_right D.h_le (by positivity)
    _ ≤ _ := by norm_num [smallRadius, backgroundAmplitude]

theorem fullCell_line_shift (q v : Space) (s : ℂ) :
    realMomentumMap q + s • realMomentumMap v =
      shiftedMomentum (fun j => q j + s.re * v j) (fun j => s.im * v j) := by
  funext j
  apply Complex.ext <;>
    simp [shiftedMomentum, realMomentum, realMomentumMap, Complex.mul_re, Complex.mul_im]

theorem fullCell_line_real_bound {h z : ℝ} (D : Calibration h z)
    {q v : Space} (hq : ‖realMomentumMap q‖ ≤ 3 * smallRadius) (hv : ‖v‖ ≤ 1)
    {s : ℂ} (hs : ‖s‖ ≤ fullCellRadius h) :
    ‖realMomentum (fun j => q j + s.re * v j)‖ ≤ 4 * smallRadius := by
  have he : realMomentum (fun j => q j + s.re * v j) =
      realMomentumMap q + (s.re : ℂ) • realMomentumMap v := by
    funext j
    simp [realMomentum, realMomentumMap]
  rw [he]
  calc
    _ ≤ ‖realMomentumMap q‖ + ‖(s.re : ℂ) • realMomentumMap v‖ := norm_add_le _ _
    _ = ‖realMomentumMap q‖ + |s.re| * ‖realMomentumMap v‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ 3 * smallRadius + fullCellRadius h * 1 := by
      exact add_le_add hq (mul_le_mul ((Complex.abs_re_le_norm s).trans hs)
        ((realMomentumMap_norm_le v).trans hv) (norm_nonneg _)
        (fullCellRadius_pos D.h_pos).le)
    _ ≤ _ := by linarith [fullCellRadius_le_small D]

theorem fullCell_unit_energy {v : Space} (hv : ‖v‖ ≤ 1) :
    hessianEnergy (fun j => v j) ≤ (2 : ℝ)^110 := by
  have hc (j : Fin 3) : |v j| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le v j).trans hv
  have hs (j : Fin 3) : (v j)^2 ≤ 1 := by
    nlinarith [sq_abs (v j), abs_nonneg (v j), hc j]
  have hd : dotProduct (fun j => v j) (fun j => v j) ≤ 3 := by
    simp only [dotProduct, Fin.sum_univ_three]
    nlinarith [hs 0, hs 1, hs 2]
  calc
    _ ≤ (256 / backgroundAmplitude) * dotProduct (fun j => v j) (fun j => v j) :=
      (hessian_bounds (fun j => v j)).2
    _ ≤ (256 / backgroundAmplitude) * 3 := mul_le_mul_of_nonneg_left hd
      (div_nonneg (by norm_num) backgroundAmplitude_pos.le)
    _ ≤ _ := by norm_num [backgroundAmplitude]

theorem fullCell_line_imaginary_bound {h : ℝ}
    {v : Space} (hv : ‖v‖ ≤ 1) {s : ℂ} (hs : ‖s‖ ≤ fullCellRadius h) :
    hessianEnergy (fun j => s.im * v j) ≤ (99 / 100 : ℝ)^2 * h^2 := by
  have he : (fun j => s.im * v j) = s.im • (fun j => v j) := rfl
  have hi : |s.im| ≤ fullCellRadius h := (Complex.abs_im_le_norm s).trans hs
  have hs2 : s.im^2 ≤ (fullCellRadius h)^2 := by
    nlinarith [sq_abs s.im, abs_nonneg s.im]
  rw [he, hessianEnergy_smul]
  calc
    _ ≤ (fullCellRadius h)^2 * (2 : ℝ)^110 :=
      mul_le_mul hs2 (fullCell_unit_energy hv) (hessianEnergy_nonneg _) (by positivity)
    _ = ((2 : ℝ)^110 / ((2 : ℝ)^256)^2) * h^2 := by
      unfold fullCellRadius
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg h)

theorem fullCell_line_analytic {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    {q v : Space} (hq : ‖realMomentumMap q‖ ≤ 3 * smallRadius) (hv : ‖v‖ ≤ 1) :
    AnalyticOnNhd ℂ (fun s : ℂ => fullCellSymbol z σ
      (realMomentumMap q + s • realMomentumMap v)) (closedBall 0 (fullCellRadius h)) := by
  intro s hs
  have hsn : ‖s‖ ≤ fullCellRadius h := by simpa using hs
  have ha := fullCellSymbol_tube_analyticAt D hh hσ0 hσ
    (fun j => q j + s.re * v j) (fun j => s.im * v j)
    (fullCell_line_real_bound D hq hv hsn) (fullCell_line_imaginary_bound hv hsn)
  rw [← fullCell_line_shift] at ha
  exact ha.comp (f := fun s : ℂ => realMomentumMap q + s • realMomentumMap v)
    (analyticAt_const.add (analyticAt_id.smul analyticAt_const))

theorem fullCell_line_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64)
    {q v : Space} (hq : ‖realMomentumMap q‖ ≤ 3 * smallRadius) (hv : ‖v‖ ≤ 1)
    {s : ℂ} (hs : s ∈ closedBall 0 (fullCellRadius h)) :
    ‖fullCellSymbol z σ (realMomentumMap q + s • realMomentumMap v)‖ ≤
      (2 : ℝ)^14 * (h^2)⁻¹ := by
  have hsn : ‖s‖ ≤ fullCellRadius h := by simpa using hs
  rw [fullCell_line_shift]
  exact fullCellSymbol_tube_norm_le D hh hσ0 hσ
    (fun j => q j + s.re * v j) (fun j => s.im * v j)
    (fullCell_line_real_bound D hq hv hsn) (fullCell_line_imaginary_bound hv hsn)

#print axioms fullCell_line_analytic
#print axioms fullCell_line_norm_le

end Maxwell.Continuum.CellGauge
