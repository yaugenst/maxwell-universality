import Maxwell.Continuum.CellSeparatedSymbol
import Maxwell.Continuum.CutoffAnalyticSymbol

/-! Arbitrary-order integration by parts and stretched-exponential Fourier
decay for the literal separated symbol after the physical cell gauge. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.CellGauge

open FreeFiber Auxiliary OperatorFourier Set Metric

local instance : NormedSpace ℝ CellMap := NormedSpace.complexToReal

def cutoffCellSymbol (z σ : ℝ) : Space → CellMap := cutoffSymbol (separatedCellSymbol z σ)

theorem cutoffCellSymbol_gevrey {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) (q v : Space) (hv : ‖v‖ ≤ 1) (K : ℕ) :
    ‖directionalDerivative K (cutoffCellSymbol z σ) q v‖ ≤
      (2 : ℝ)^161 * ((2 : ℝ)^157)^K * (K.factorial : ℝ)^2 := by
  have hb : ∀ q ∈ closedBall (0 : Momentum) separatedRadius,
      ‖separatedCellSymbol z σ q‖ ≤ (2 : ℝ)^116 := by
    intro q hq
    exact separatedCellSymbol_norm_le D hσ0 hσ (by simpa using hq)
  have hd := cutoffSymbol_gevrey (separatedCellSymbol z σ)
    (separatedCellSymbol_analytic D hσ0 hσ) hb (by positivity) q v hv K
  have hc : (2 : ℝ)^45 * 2^116 = 2^161 := by norm_num
  rw [hc] at hd
  exact hd

theorem cutoffCellSymbol_fourier_decay {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h^4 / 64) (p : Space) :
    ‖angularFourier (cutoffCellSymbol z σ) p‖ ≤
      24 * (2 : ℝ)^161 * Real.exp (-Real.sqrt (400 * ‖p‖ / (2 : ℝ)^157) / 64) := by
  have hb : ∀ q ∈ closedBall (0 : Momentum) separatedRadius,
      ‖separatedCellSymbol z σ q‖ ≤ (2 : ℝ)^116 := by
    intro q hq
    exact separatedCellSymbol_norm_le D hσ0 hσ (by simpa using hq)
  have hd := cutoffSymbol_fourier_decay (separatedCellSymbol z σ)
    (separatedCellSymbol_analytic D hσ0 hσ) hb (by positivity) p
  have hc : (2 : ℝ)^45 * 2^116 = 2^161 := by norm_num
  rw [hc] at hd
  exact hd

#print axioms cutoffCellSymbol_gevrey
#print axioms cutoffCellSymbol_fourier_decay

end Maxwell.Continuum.CellGauge
