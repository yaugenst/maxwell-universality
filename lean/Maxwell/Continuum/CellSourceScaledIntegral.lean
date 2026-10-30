import Maxwell.Continuum.CellSourcePhaseScaling
import Maxwell.Continuum.PeriodicSelectedSplit
import Maxwell.Continuum.PeriodicSeparatedFourier

/-! Exact rescaling of the limiting source contour integral to the
selected scalar quotient plus the other-band source symbol. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.CellGauge

open Complex FreeFiber PeriodicBand EffectiveMass Auxiliary AlmostAnalytic MeasureTheory

attribute [local irreducible] fullCellSymbol separatedCellSymbol realMode selectedGlobalQuotient

theorem scaled_source_cutoff_pole {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) {k : Space} (hk0 : k ≠ 0) :
    (h : ℂ)^5*((64*blochDensity : ℝ) : ℂ)*scaledPoleCutoff D hh j k*
      cellSourcePairing h (realMode D hh) (realMode D hh) (fullCellSymbol z 0)
        (poleMomentum D hh j (realMomentum k.ofLp)) =
      cutoffSelectedQuotient D hh j k+
        separatedRegularSymbol D hh j (realMode D hh) (realMode D hh) k := by
  by_cases hk : h*‖k‖ ≤ 4*smallRadius
  · have hq := globalPole_unit_line_chart D hh j k hk (v := (0 : Momentum)) (by simp)
      (ζ := (0 : ℂ)) (by norm_num)
    simp only [zero_smul, add_zero] at hq
    have hc : poleMomentum D hh j (realMomentum k.ofLp) ∈ physicalChart := by
      intro i
      have hb := globalPole_source_physical D hh j k hk
      rw [scaledPoleCenter_physical] at hb
      exact (norm_le_pi_norm _ i).trans_lt (hb.trans_lt (by linarith only [analyticRadius_pos]))
    have hn : dielectricBand (poleMomentum D hh j (realMomentum k.ofLp))-(z : ℂ) ≠ 0 := by
      intro he
      apply globalPole_denominator_ne_zero D hh j hk hk0
      rw [poleDenominator, he, mul_zero]
    have hp := scaled_source_symbol_pole D hh j (realMomentum k.ofLp) hq hc hn
    calc
      _ = scaledPoleCutoff D hh j k*((h : ℂ)^5*((64*blochDensity : ℝ) : ℂ)*
          cellSourcePairing h (realMode D hh) (realMode D hh) (fullCellSymbol z 0)
            (poleMomentum D hh j (realMomentum k.ofLp))) := by ring
      _ = _ := by rw [hp]; unfold cutoffSelectedQuotient separatedRegularSymbol; ring
  · rw [scaledPoleCutoff_zero_outside D hh j (lt_of_not_ge hk), mul_zero, zero_mul,
      cutoffSelectedQuotient_zero_outside D hh j (lt_of_not_ge hk),
      separatedRegularSymbol_zero_outside D hh j _ _ (lt_of_not_ge hk), add_zero]

theorem sourcePoleContour_scaled_integrand {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) (d : ℝ) {k : Space} (hk0 : k ≠ 0) :
    (h : ℂ)^5*((64*blochDensity : ℝ) : ℂ)*
      sourcePoleContourIntegrand D hh j (realMode D hh) (realMode D hh)
        (poleAxialDisplacement h d j) 1 (h • k) =
      (Real.exp (-poleAction D hh j*d) : ℂ)*
        (OperatorFourier.angularPhase k (-(2*(placementDiagonal j : ℝ)*d) • PiLp.single 2 j 1)*
          (cutoffSelectedQuotient D hh j k+
            separatedRegularSymbol D hh j (realMode D hh) (realMode D hh) k)) := by
  unfold sourcePoleContourIntegrand contourProduct phasedSymbol
  rw [poleContour_scaled_phase, poleContour_scaled_momentum]
  change (h : ℂ)^5*((64*blochDensity : ℝ) : ℂ)*
    (scaledPoleCutoff D hh j k*((Real.exp (-poleAction D hh j*d) : ℂ)*
      OperatorFourier.angularPhase k (-(2*(placementDiagonal j : ℝ)*d) • PiLp.single 2 j 1)*
      cellSourcePairing h (realMode D hh) (realMode D hh) (fullCellSymbol z 0)
        (poleMomentum D hh j (realMomentum k.ofLp)))) = _
  rw [show (h : ℂ)^5*((64*blochDensity : ℝ) : ℂ)*
      (scaledPoleCutoff D hh j k*((Real.exp (-poleAction D hh j*d) : ℂ)*
        OperatorFourier.angularPhase k (-(2*(placementDiagonal j : ℝ)*d) • PiLp.single 2 j 1)*
        cellSourcePairing h (realMode D hh) (realMode D hh) (fullCellSymbol z 0)
          (poleMomentum D hh j (realMomentum k.ofLp)))) =
      (Real.exp (-poleAction D hh j*d) : ℂ)*
        (OperatorFourier.angularPhase k (-(2*(placementDiagonal j : ℝ)*d) • PiLp.single 2 j 1)*
          ((h : ℂ)^5*((64*blochDensity : ℝ) : ℂ)*scaledPoleCutoff D hh j k*
            cellSourcePairing h (realMode D hh) (realMode D hh) (fullCellSymbol z 0)
              (poleMomentum D hh j (realMomentum k.ofLp)))) by ring]
  rw [scaled_source_cutoff_pole D hh j hk0]

theorem sourcePoleContour_scaled_integral {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) (d : ℝ) :
    (h : ℂ)^2*((64*blochDensity : ℝ) : ℂ)*
      (∫ q, sourcePoleContourIntegrand D hh j (realMode D hh) (realMode D hh)
        (poleAxialDisplacement h d j) 1 q) =
      (Real.exp (-poleAction D hh j*d) : ℂ)*
        OperatorFourier.angularFourier
          (fun k => cutoffSelectedQuotient D hh j k+
            separatedRegularSymbol D hh j (realMode D hh) (realMode D hh) k)
          (-(2*(placementDiagonal j : ℝ)*d) • PiLp.single 2 j 1) := by
  let F := sourcePoleContourIntegrand D hh j (realMode D hh) (realMode D hh)
    (poleAxialDisplacement h d j) 1
  have he : (∫ k : Space, (h : ℂ)^5*((64*blochDensity : ℝ) : ℂ)*F (h • k)) =
      ∫ k : Space, (Real.exp (-poleAction D hh j*d) : ℂ)*
        (OperatorFourier.angularPhase k (-(2*(placementDiagonal j : ℝ)*d) • PiLp.single 2 j 1)*
          (cutoffSelectedQuotient D hh j k+
            separatedRegularSymbol D hh j (realMode D hh) (realMode D hh) k)) := by
    apply integral_congr_ae
    filter_upwards [volume.ae_ne (0 : Space)] with k hk
    exact sourcePoleContour_scaled_integrand D hh j d hk
  rw [integral_const_mul, integral_const_mul] at he
  have hc := Measure.integral_comp_smul_of_nonneg (volume : Measure Space) F h (hR := D.h_pos.le)
  rw [show Module.finrank ℝ Space = 3 from finrank_euclideanSpace_fin] at hc
  rw [hc, Complex.real_smul] at he
  rw [OperatorFourier.angularFourier_integral]
  change (h : ℂ)^2*((64*blochDensity : ℝ) : ℂ)*(∫ q, F q) = _
  convert he using 1
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr D.h_pos.ne']

#print axioms sourcePoleContour_scaled_integral

end Maxwell.Continuum.CellGauge
