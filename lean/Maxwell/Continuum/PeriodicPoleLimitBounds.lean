import Maxwell.Continuum.PeriodicPoleLimitDenominator
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-! An actual locally integrable operator-norm majorant for the limiting
pole contour. It controls all parameters up to and including the limit,
away from the single Lebesgue-null momentum at the pole. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric MeasureTheory

attribute [local irreducible] dielectricBand fullFiberResolvent CellGauge.fullCellSymbol imaginaryPole

def poleLimitMajorant (q : Space) : ℝ := (2 : ℝ)^120 * (1 + (‖q‖^2)⁻¹)

theorem poleLimitMajorant_nonneg (q : Space) : 0 ≤ poleLimitMajorant q := by
  unfold poleLimitMajorant
  positivity

theorem euclidean_norm_pos_of_ne_zero {q : Corner.Vec} (hq : q ≠ 0) :
    0 < ‖(WithLp.toLp 2 q : Space)‖ := by
  apply norm_pos_iff.mpr
  intro he
  apply hq
  exact congrArg (fun v : Space => v.ofLp) he

theorem pole_path_inverse_norm_le {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) (hq0 : q ≠ 0) :
    ‖(dielectricBand (shiftedMomentum q (axialPoleShift D hh j s)) - (z : ℂ))⁻¹‖ ≤
      2 * (‖(WithLp.toLp 2 q : Space)‖^2)⁻¹ := by
  have hl : ‖(WithLp.toLp 2 q : Space)‖^2 / 2 ≤
      ‖dielectricBand (shiftedMomentum q (axialPoleShift D hh j s)) - (z : ℂ)‖ := by
    calc
      _ ≤ hessianEnergy q / 2 :=
        div_le_div_of_nonneg_right (euclidean_norm_sq_le_hessianEnergy q) (by norm_num)
      _ ≤ (dielectricBand (shiftedMomentum q (axialPoleShift D hh j s)) - (z : ℂ)).re :=
        pole_path_denominator_lower D hh j hs q hq
      _ ≤ _ := Complex.re_le_norm _
  rw [norm_inv]
  exact (inv_anti₀ (div_pos (sq_pos_of_pos (euclidean_norm_pos_of_ne_zero hq0))
    (by norm_num)) hl).trans_eq (by ring)

theorem pole_path_fiber_norm_le {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) (hq0 : q ≠ 0) :
    ‖fullFiberResolvent z 0 (shiftedMomentum q (axialPoleShift D hh j s))‖ ≤
      (2 : ℝ)^113 * (1 + (‖(WithLp.toLp 2 q : Space)‖^2)⁻¹) := by
  have hσ : (0 : ℝ) ≤ h^4 / 64 := by positivity
  have hqs := wide_tube_chart_radius D.h_pos.le hh q _ hq (axialPoleShift_energy D hh j hs)
  have hne : dielectricBand (shiftedMomentum q (axialPoleShift D hh j s)) -
      ((z + 0 : ℝ) : ℂ) ≠ 0 := by
    simpa only [add_zero] using pole_path_denominator_ne_zero D hh j hs q hq hq0
  have hp := fullFiberResolvent_norm_le_pole D le_rfl hσ hqs hne
  simp only [add_zero] at hp
  calc
    _ ≤ (2 * (‖(WithLp.toLp 2 q : Space)‖^2)⁻¹) * (81 / 25) + (2 : ℝ)^112 := by
      apply hp.trans
      gcongr
      exact pole_path_inverse_norm_le D hh j hs q hq hq0
    _ ≤ _ := by
      have hx : 0 ≤ (‖(WithLp.toLp 2 q : Space)‖^2)⁻¹ := inv_nonneg.mpr (sq_nonneg _)
      norm_num
      nlinarith

theorem pole_path_cell_norm_le {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) (hq0 : q ≠ 0) :
    ‖CellGauge.fullCellSymbol z 0 (shiftedMomentum q (axialPoleShift D hh j s))‖ ≤
      poleLimitMajorant (WithLp.toLp 2 q) := by
  have hqs := wide_tube_chart_radius D.h_pos.le hh q _ hq (axialPoleShift_energy D hh j hs)
  have hg := CellGauge.cellGauge_small_bound hqs
  have hf := (CellGauge.conjugate_bound (fullFiberResolvent z 0
    (shiftedMomentum q (axialPoleShift D hh j s)))).trans
      (pole_path_fiber_norm_le D hh j hs q hq hq0)
  unfold CellGauge.fullCellSymbol poleLimitMajorant
  calc
    _ ≤ ‖CellGauge.antiGauge (shiftedMomentum q (axialPoleShift D hh j s))‖ *
        ‖(CellGauge.conjugate (fullFiberResolvent z 0 (shiftedMomentum q (axialPoleShift D hh j s)))).comp
          (CellGauge.antiUngauge (shiftedMomentum q (axialPoleShift D hh j s)))‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 3 * (((2 : ℝ)^113 * (1 + (‖(WithLp.toLp 2 q : Space)‖^2)⁻¹)) * 3) := by
      apply mul_le_mul hg.1 _ (norm_nonneg _) (by norm_num)
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul hf hg.2 (norm_nonneg _) (by positivity))
    _ = (9 * (2 : ℝ)^113) * (1 + (‖(WithLp.toLp 2 q : Space)‖^2)⁻¹) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)

theorem pole_path_cell_analyticAt {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) (hq0 : q ≠ 0) :
    AnalyticAt ℂ (CellGauge.fullCellSymbol z 0)
      (shiftedMomentum q (axialPoleShift D hh j s)) := by
  apply CellGauge.fullCellSymbol_analyticAt D le_rfl (by positivity)
    (wide_tube_chart_radius D.h_pos.le hh q _ hq (axialPoleShift_energy D hh j hs))
  simpa only [add_zero] using pole_path_denominator_ne_zero D hh j hs q hq hq0

theorem poleLimitMajorant_integrableOn_ball (r : ℝ) :
    IntegrableOn poleLimitMajorant (ball (0 : Space) r) volume := by
  have hm : Measurable (fun q : Space => (‖q‖^2)⁻¹) := by fun_prop
  have hi : IntegrableOn (fun q : Space => (‖q‖^2)⁻¹) (ball 0 r) volume := by
    apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := 2)
      (by simp [Space]) (by norm_num [Space]) _ hm.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun q => by
      rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg _)), one_mul,
        Real.rpow_neg (norm_nonneg q), Real.rpow_two])
  have hc : IntegrableOn (fun _ : Space => (1 : ℝ)) (ball 0 r) volume :=
    (integrableOn_const (isCompact_closedBall (0 : Space) r).measure_lt_top.ne).mono_set
      ball_subset_closedBall
  exact (hc.add hi).const_mul ((2 : ℝ)^120)

end Maxwell.Continuum.PeriodicBand
