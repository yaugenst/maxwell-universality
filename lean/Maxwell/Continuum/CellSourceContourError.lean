import Maxwell.Continuum.CellSourceContour
import Maxwell.Continuum.AlmostAnalyticPartialContour

/-! Exponentially small contour error for the literal compact-source
matrix element, proved up to the singular endpoint. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096
set_option maxRecDepth 2048

namespace Maxwell.Continuum.CellGauge

open Complex FreeFiber PeriodicBand Auxiliary AlmostAnalytic MasterConstants Set MeasureTheory Filter
open scoped Topology

attribute [local irreducible] fullCellSymbol

theorem sourcePoleContour_partial_error {L z : ℝ} (hL : Ls ≤ L)
    (D : Calibration L⁻¹ z) (j : Fin 3) {u v : FieldL2}
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (R : Space)
    (hphase : 0 ≤ inner ℝ (poleContourShift D (inverse_length_le_1024 hL) j) R)
    {s : ℝ} (hs : s ∈ Ico (0 : ℝ) 1) :
    ‖(∫ q, sourcePoleContourIntegrand D (inverse_length_le_1024 hL) j u v R s q)-
      (∫ q, sourcePoleContourIntegrand D (inverse_length_le_1024 hL) j u v R 0 q)‖ ≤
        (2 : ℝ)^335*L^3*Real.exp (-cs*L) := by
  let hh := inverse_length_le_1024 hL
  let β := poleContourShift D hh j
  let Y := cellSourcePairing L⁻¹ u v (fullCellSymbol z 0)
  have hL0 : 0 < L := inv_pos.mp D.h_pos
  have ha : ∀ t ∈ Icc (0 : ℝ) s, ∀ q, ‖q‖ ≤ 4*smallRadius →
      AnalyticAt ℂ (phasedSymbol R Y) (AlmostAnalytic.shiftedMomentum q β t) := by
    intro t ht q hq
    exact phasedSymbol_analyticAt R (cellSourcePairing_analytic L⁻¹ u v
      (poleContour_symbol_analytic_before D hh j ⟨ht.1, lt_of_le_of_lt ht.2 hs.2⟩ q hq))
  have hb : ∀ t ∈ Icc (0 : ℝ) s, ∀ q : Space, smallRadius ≤ ‖q‖ →
      ‖q‖ ≤ 4*smallRadius →
      ‖phasedSymbol R Y (AlmostAnalytic.shiftedMomentum q β t)‖ ≤ (2 : ℝ)^286*L^3 := by
    intro t ht q hq0 hq
    rw [phasedSymbol_shifted_norm]
    have he : Real.exp (-t*inner ℝ β R) ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht.1) hphase)
    have hp := cellSourcePairing_tube_norm D.h_pos (hh.trans (by norm_num)) hu hv
      (sourceImaginary_poleContour D hh j q ⟨ht.1, ht.2.trans hs.2.le⟩) (fullCellSymbol z 0)
    simp only [inv_inv] at hp
    apply (mul_le_mul he hp (norm_nonneg _) (by norm_num)).trans
    rw [one_mul]
    calc
      _ ≤ (2 : ℝ)^90*L^3*(2 : ℝ)^196 :=
        mul_le_mul_of_nonneg_left (poleContour_transition_bound D hh j
          ⟨ht.1, ht.2.trans hs.2.le⟩ q hq0 hq) (by positivity)
      _ = _ := by rw [show (286 : ℕ) = 90+196 by omega, pow_add]; ring
  have he := partial_contour_integral_error_bound hL (poleContourShift_norm_le D hh j)
    (poleContourShift_ne_zero D hh j) (phasedSymbol R Y)
    (show 0 ≤ (2 : ℝ)^286*L^3 by positivity) ⟨hs.1, hs.2.le⟩ ha hb
  change ‖(∫ q, contourProduct (cutoffOrder β) β (phasedSymbol R Y) s q)-
    (∫ q, contourProduct (cutoffOrder β) β (phasedSymbol R Y) 0 q)‖ ≤ _
  apply he.trans_eq
  rw [show (335 : ℕ) = 49+286 by omega, pow_add]
  ring

theorem sourcePoleContour_endpoint_error {L z : ℝ} (hL : Ls ≤ L)
    (D : Calibration L⁻¹ z) (j : Fin 3) {u v : FieldL2}
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (R : Space)
    (hphase : 0 ≤ inner ℝ (poleContourShift D (inverse_length_le_1024 hL) j) R) :
    ‖(∫ q, sourcePoleContourIntegrand D (inverse_length_le_1024 hL) j u v R 1 q)-
      OperatorFourier.angularFourier
        (fun q => (Well.chi smallRadius q : ℂ)*cellSourcePairing L⁻¹ u v
          (fullCellSymbol z 0) (realMomentumMap q)) (-R)‖ ≤
            (2 : ℝ)^335*L^3*Real.exp (-cs*L) := by
  have hi : (∫ q, sourcePoleContourIntegrand D (inverse_length_le_1024 hL) j u v R 0 q) =
      OperatorFourier.angularFourier
        (fun q => (Well.chi smallRadius q : ℂ)*cellSourcePairing L⁻¹ u v
          (fullCellSymbol z 0) (realMomentumMap q)) (-R) :=
    initial_integral_eq _ _ _ _
  rw [← hi]
  have hl := ((sourcePoleContour_integral_tendsto D (inverse_length_le_1024 hL) j hu hv R hphase).sub_const
    (∫ q, sourcePoleContourIntegrand D (inverse_length_le_1024 hL) j u v R 0 q)).norm
  apply le_of_tendsto hl
  rw [← nhdsWithin_Ico_eq_nhdsLT (show (0 : ℝ) < 1 by norm_num)]
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact sourcePoleContour_partial_error hL D j hu hv R hphase hs

#print axioms sourcePoleContour_endpoint_error

end Maxwell.Continuum.CellGauge
