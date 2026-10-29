import Maxwell.Continuum.SeparatedCellKernel

/-! Actual arbitrary-order polynomial cell decay of the separated inverse.
The order remains symbolic, so finite-order source-coupling estimates can
reuse this endpoint without redoing integration by parts. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellGauge

open Auxiliary OperatorFourier FreeFiber PeriodicBand Metric Set

local instance : NormedSpace ℝ CellMap := NormedSpace.complexToReal

theorem separatedCellBlock_polynomial {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) (a b : Bloch.Alias) (K : ℕ) :
    ‖latticeShift b - latticeShift a‖^K * ‖separatedCellBlock D hσ0 hσ a b‖ ≤
      (2 : ℝ)^170 * ((2 : ℝ)^157)^K * (K.factorial : ℝ)^2 := by
  have hf : ContDiff ℝ (⊤ : ℕ∞) (cutoffCellSymbol z σ) :=
    cutoffSymbol_contDiff (separatedCellSymbol z σ) (separatedCellSymbol_analytic D hσ0 hσ)
  have hs : tsupport (cutoffCellSymbol z σ) ⊆ closedBall (0 : Space) 1 :=
    (cutoffSymbol_tsupport (separatedCellSymbol z σ)).trans
      (closedBall_subset_closedBall (by norm_num [smallRadius, backgroundAmplitude]))
  have hK := angularFourier_gevrey_bound (cutoffCellSymbol z σ) hf
    (cutoffSymbol_compact (separatedCellSymbol z σ)) hs
    (by positivity : (0 : ℝ) ≤ 2^161) (by positivity : (0 : ℝ) ≤ 2^157)
    (fun k q v hv => cutoffCellSymbol_gevrey D hσ0 hσ q v hv k)
    (latticeShift b - latticeShift a) K
  rw [separatedCellBlock_eq, norm_smul, norm_mul, CellBandFourier.carrier_norm,
    mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos (by norm_num) blochDensity_pos)]
  calc
    _ = (64 * blochDensity) *
        (‖latticeShift b - latticeShift a‖^K *
          ‖angularFourier (cutoffCellSymbol z σ) (latticeShift b - latticeShift a)‖) := by ring
    _ ≤ 64 * (8 * (2 : ℝ)^161 * ((2 : ℝ)^157)^K * (K.factorial : ℝ)^2) :=
      mul_le_mul (by nlinarith [blochDensity_le_one]) hK (by positivity) (by norm_num)
    _ = _ := by
      have hc : (64 : ℝ) * (8 * 2^161) = 2^170 := by norm_num
      rw [show (64 : ℝ) * (8 * 2^161 * ((2 : ℝ)^157)^K * (K.factorial : ℝ)^2) =
        (64 * (8 * 2^161)) * ((2 : ℝ)^157)^K * (K.factorial : ℝ)^2 by ring, hc]

theorem separatedCellBlock_order16 {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) (a b : Bloch.Alias) :
    ‖latticeShift b - latticeShift a‖^16 * ‖separatedCellBlock D hσ0 hσ a b‖ ≤
      (2 : ℝ)^2810 := by
  have hb := separatedCellBlock_polynomial D hσ0 hσ a b 16
  apply hb.trans
  have hf : (Nat.factorial 16 : ℝ) ≤ (2 : ℝ)^64 := by norm_num
  calc
    _ ≤ (2 : ℝ)^170 * ((2 : ℝ)^157)^16 * ((2 : ℝ)^64)^2 := by gcongr
    _ = (2 : ℝ)^2810 := by
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]

#print axioms separatedCellBlock_polynomial
#print axioms separatedCellBlock_order16

end Maxwell.Continuum.CellGauge
