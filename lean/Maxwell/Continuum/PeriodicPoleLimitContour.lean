import Maxwell.Continuum.PeriodicPoleLimitBounds
import Maxwell.Continuum.AlmostAnalyticFourierBound
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The literal operator-valued contour integrand along the actual axial
pole path. The almost-analytic truncation order stays fixed throughout
the path, including its singular limiting endpoint. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary AlmostAnalytic CellGauge Set Metric MeasureTheory Filter
open scoped Topology

attribute [local irreducible] imaginaryPole fullCellSymbol dielectricBand

def poleContourShift {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) : Space :=
  WithLp.toLp 2 (Pi.single j (imaginaryPole D hh j))

theorem poleContourShift_ne_zero {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) : poleContourShift D hh j ≠ 0 := by
  intro he
  have hj := congrArg (fun v : Space => v j) he
  simp only [poleContourShift, Pi.single_eq_same, PiLp.zero_apply] at hj
  exact (imaginaryPole_pos D hh j).ne' hj

theorem poleContourShift_momentum {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (q : Space) (s : ℝ) :
    AlmostAnalytic.shiftedMomentum q (poleContourShift D hh j) s =
      PeriodicBand.shiftedMomentum q.ofLp (axialPoleShift D hh j s) := by
  funext k
  simp only [AlmostAnalytic.shiftedMomentum, realMomentumMap,
    ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply, PiLp.proj_apply,
    Complex.ofRealCLM_apply, PeriodicBand.shiftedMomentum, realMomentum,
    axialPoleShift, poleContourShift, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Complex.ofReal_mul]
  change (q k : ℂ) + Complex.I * (s : ℂ) *
    (((Pi.single j (imaginaryPole D hh j) : Corner.Vec) k : ℝ) : ℂ) = _
  ring

theorem poleContour_ofLp_ne_zero {q : Space} (hq : q ≠ 0) : q.ofLp ≠ 0 := by
  intro he
  apply hq
  exact congrArg (WithLp.toLp 2) he

theorem poleContour_chart {q : Space} (hq : ‖q‖ ≤ 4*smallRadius) :
    ‖realMomentum q.ofLp‖ ≤ 4*smallRadius :=
  (realMomentum_norm_le_euclidean q.ofLp).trans hq

def poleContourIntegrand {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (R : Space) (s : ℝ) (q : Space) : CellMap :=
  contourProduct (cutoffOrder (poleContourShift D hh j)) (poleContourShift D hh j)
    (phasedSymbol R (fullCellSymbol z 0)) s q

theorem poleContour_symbol_analytic_before {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1)
    (q : Space) (hq : ‖q‖ ≤ 4*smallRadius) :
    AnalyticAt ℂ (fullCellSymbol z 0)
      (AlmostAnalytic.shiftedMomentum q (poleContourShift D hh j) s) := by
  rw [poleContourShift_momentum]
  apply fullCellSymbol_analyticAt D le_rfl (by positivity)
    (wide_tube_chart_radius D.h_pos.le hh q.ofLp _ (poleContour_chart hq)
      (axialPoleShift_energy D hh j ⟨hs.1, hs.2.le⟩))
  simpa only [add_zero] using pole_path_denominator_ne_zero_before D hh j hs
    q.ofLp (poleContour_chart hq)

theorem poleContourIntegrand_contDiff {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (R : Space)
    {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) :
    ContDiff ℝ (⊤ : ℕ∞) (poleContourIntegrand D hh j R s) := by
  apply contourProduct_contDiff
  intro q hq
  exact phasedSymbol_analyticAt R (poleContour_symbol_analytic_before D hh j hs q hq)

theorem poleContourIntegrand_joint_continuousAt {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (R : Space)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {q : Space} (hq0 : q ≠ 0) :
    ContinuousAt (Function.uncurry (poleContourIntegrand D hh j R)) (s,q) := by
  have hc := contourProduct_joint_contDiffAt
    (cutoffOrder (poleContourShift D hh j)) (poleContourShift D hh j)
    (phasedSymbol R (fullCellSymbol z 0)) (s,q) (fun hq => by
      apply phasedSymbol_analyticAt R
      rw [poleContourShift_momentum]
      exact pole_path_cell_analyticAt D hh j hs q.ofLp (poleContour_chart hq)
        (poleContour_ofLp_ne_zero hq0))
  exact hc.continuousAt

theorem poleContourIntegrand_continuousAt_parameter {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (R : Space)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {q : Space} (hq0 : q ≠ 0) :
    ContinuousAt (fun t : ℝ => poleContourIntegrand D hh j R t q) s := by
  exact ContinuousAt.comp (f := fun t : ℝ => (t,q)) (x := s)
    (poleContourIntegrand_joint_continuousAt D hh j R hs hq0)
    (continuousAt_id.prodMk continuousAt_const)

theorem poleContourIntegrand_continuousAt_spatial {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (R : Space)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {q : Space} (hq0 : q ≠ 0) :
    ContinuousAt (poleContourIntegrand D hh j R s) q := by
  exact ContinuousAt.comp (f := fun p : Space => (s,p)) (x := q)
    (poleContourIntegrand_joint_continuousAt D hh j R hs hq0)
    (continuousAt_const.prodMk continuousAt_id)

def poleContourMajorant (q : Space) : ℝ :=
  (closedBall (0 : Space) (4*smallRadius)).indicator
    (fun p => (2 : ℝ)^46 * poleLimitMajorant p) q

theorem poleContourMajorant_nonneg (q : Space) : 0 ≤ poleContourMajorant q := by
  apply Set.indicator_nonneg
  intro p _
  exact mul_nonneg (by positivity) (poleLimitMajorant_nonneg p)

theorem poleContourMajorant_integrable : Integrable poleContourMajorant volume := by
  apply (integrable_indicator_iff measurableSet_closedBall).mpr
  apply Integrable.const_mul
  exact (poleLimitMajorant_integrableOn_ball (4*smallRadius+1)).mono_set
    (closedBall_subset_ball (by linarith))

theorem poleContourIntegrand_norm_le {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (R : Space)
    (hphase : 0 ≤ inner ℝ (poleContourShift D hh j) R)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {q : Space} (hq0 : q ≠ 0) :
    ‖poleContourIntegrand D hh j R s q‖ ≤ poleContourMajorant q := by
  by_cases hq : ‖q‖ ≤ 4*smallRadius
  · have hmem : q ∈ closedBall (0 : Space) (4*smallRadius) := by
      simpa only [mem_closedBall, dist_zero_right] using hq
    rw [poleContourMajorant, Set.indicator_of_mem hmem, poleContourIntegrand,
      contourProduct, norm_smul, phasedSymbol_shifted_norm]
    have hc := cutoffTaylor_norm_le (poleContourShift_ne_zero D hh j) q
      (show |s| ≤ 1 by rw [abs_of_nonneg hs.1]; exact hs.2)
    have he : Real.exp (-s*inner ℝ (poleContourShift D hh j) R) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.1) hphase)
    have hy : ‖fullCellSymbol z 0
        (AlmostAnalytic.shiftedMomentum q (poleContourShift D hh j) s)‖ ≤
        poleLimitMajorant q := by
      rw [poleContourShift_momentum]
      exact pole_path_cell_norm_le D hh j hs q.ofLp (poleContour_chart hq)
        (poleContour_ofLp_ne_zero hq0)
    exact mul_le_mul hc ((mul_le_mul he hy (norm_nonneg _) (by norm_num)).trans_eq
      (one_mul _)) (by positivity) (by positivity)
  · rw [poleContourIntegrand, contourProduct_zero_outside _ _ _ _ (lt_of_not_ge hq), norm_zero]
    exact poleContourMajorant_nonneg q

end Maxwell.Continuum.PeriodicBand
