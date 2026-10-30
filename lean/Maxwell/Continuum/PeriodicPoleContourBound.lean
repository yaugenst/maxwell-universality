import Maxwell.Continuum.PeriodicPoleContourGeometry
import Maxwell.Continuum.AlmostAnalyticPartialContour

/-! Actual contour movement up to the selected imaginary pole. The
finite shifts have a common exponentially small defect bound, and the
proved Bochner dominated-convergence theorem supplies the endpoint. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096

namespace Maxwell.Continuum.PeriodicBand

open Complex FreeFiber Auxiliary AlmostAnalytic CellGauge MasterConstants Set MeasureTheory Filter
open scoped Topology

attribute [local irreducible] imaginaryPole fullCellSymbol

theorem poleContour_partial_error {L z : ℝ} (hL : Ls ≤ L)
    (D : Calibration L⁻¹ z) (j : Fin 3) (R : Space)
    (hphase : 0 ≤ inner ℝ (poleContourShift D (inverse_length_le_1024 hL) j) R)
    {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) :
    ‖(∫ q, poleContourIntegrand D (inverse_length_le_1024 hL) j R s q) -
      (∫ q, poleContourIntegrand D (inverse_length_le_1024 hL) j R 0 q)‖ ≤
        (2 : ℝ)^245*Real.exp (-cs*L) := by
  let hh := inverse_length_le_1024 hL
  let β := poleContourShift D hh j
  have ha : ∀ t ∈ Icc (0 : ℝ) s, ∀ q, ‖q‖ ≤ 4*smallRadius →
      AnalyticAt ℂ (phasedSymbol R (fullCellSymbol z 0)) (AlmostAnalytic.shiftedMomentum q β t) := by
    intro t ht q hq
    exact phasedSymbol_analyticAt R (poleContour_symbol_analytic_before D hh j
      ⟨ht.1, lt_of_le_of_lt ht.2 hs.2⟩ q hq)
  have hb : ∀ t ∈ Icc (0 : ℝ) s, ∀ q : Space, smallRadius ≤ ‖q‖ →
      ‖q‖ ≤ 4*smallRadius →
      ‖phasedSymbol R (fullCellSymbol z 0) (AlmostAnalytic.shiftedMomentum q β t)‖ ≤ (2 : ℝ)^196 := by
    intro t ht q hq0 hq
    rw [phasedSymbol_shifted_norm]
    have he : Real.exp (-t*inner ℝ β R) ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht.1) hphase)
    exact (mul_le_mul he (poleContour_transition_bound D hh j ⟨ht.1, ht.2.trans hs.2.le⟩ q hq0 hq)
      (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have he := partial_contour_integral_error_bound hL (poleContourShift_norm_le D hh j)
    (poleContourShift_ne_zero D hh j) (phasedSymbol R (fullCellSymbol z 0))
    (by positivity : 0 ≤ (2 : ℝ)^196) ⟨hs.1, hs.2.le⟩ ha hb
  change ‖(∫ q, contourProduct (cutoffOrder β) β (phasedSymbol R (fullCellSymbol z 0)) s q) -
    (∫ q, contourProduct (cutoffOrder β) β (phasedSymbol R (fullCellSymbol z 0)) 0 q)‖ ≤ _
  apply he.trans_eq
  ring

theorem poleContour_endpoint_error {L z : ℝ} (hL : Ls ≤ L)
    (D : Calibration L⁻¹ z) (j : Fin 3) (R : Space)
    (hphase : 0 ≤ inner ℝ (poleContourShift D (inverse_length_le_1024 hL) j) R) :
    ‖(∫ q, poleContourIntegrand D (inverse_length_le_1024 hL) j R 1 q) -
      OperatorFourier.angularFourier
        (fun q => (Well.chi smallRadius q : ℂ) • fullCellSymbol z 0 (realMomentumMap q)) (-R)‖ ≤
          (2 : ℝ)^245*Real.exp (-cs*L) := by
  rw [← poleContour_initial_integral D (inverse_length_le_1024 hL) j R]
  have hl := ((poleContour_integral_tendsto D (inverse_length_le_1024 hL) j R hphase).sub_const
    (∫ q, poleContourIntegrand D (inverse_length_le_1024 hL) j R 0 q)).norm
  apply le_of_tendsto hl
  rw [← nhdsWithin_Ico_eq_nhdsLT (show (0 : ℝ) < 1 by norm_num)]
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact poleContour_partial_error hL D j R hphase hs

#print axioms poleContour_endpoint_error

end Maxwell.Continuum.PeriodicBand
