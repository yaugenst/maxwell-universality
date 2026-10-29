import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! Rational replacement budgets for the larger residual of the Lppp
Feshbach basis. The remaining two L-point residuals are smaller, so these
same upper budgets also apply to them. -/
namespace Maxwell.Certificate.OtherPointBudgets

noncomputable section

def residualRadius : ℝ := 1/2^44
def frameEpsilon : ℝ := 1/2^36
def frameError : ℝ := 1/2^32
def spectralGap : ℝ := 11/2000
def energyGap : ℝ := spectralGap-residualRadius
def correctorError : ℝ := 1/2^23

theorem energyGap_pos : 0 < energyGap := by
  norm_num [energyGap, spectralGap, residualRadius]

theorem frame_epsilon_pos_small : 0 < frameEpsilon ∧ frameEpsilon ≤ 1/32 := by
  norm_num [frameEpsilon]

theorem frame_error_eq : 16*frameEpsilon = frameError := by
  norm_num [frameEpsilon, frameError]

theorem gram_error_le : (1/10^12 : ℝ) ≤ frameEpsilon := by
  norm_num [frameEpsilon]

/-- A verified near-unit point column has norm at most `11/10`. -/
theorem column_norm_le {n : ℝ} (hn : 0 ≤ n) (h : n^2 ≤ 1+1/10^12) : n ≤ 11/10 := by
  nlinarith

theorem projection_budget : residualRadius/spectralGap*(11/10) ≤ frameEpsilon := by
  norm_num [residualRadius, spectralGap, frameEpsilon]

theorem corrector_error_budget :
    ((1/10^11 : ℝ)+residualRadius*(2909/1000)+(11/5)*frameError)/energyGap ≤
      correctorError := by
  norm_num [residualRadius, frameError, energyGap, spectralGap, correctorError]

theorem corrector_norm_budget : (2909/1000 : ℝ)+correctorError ≤ 3 := by
  norm_num [correctorError]

/-- The wider frame/corrector errors preserve the same compressed-jet
replacement budget used for the selected point. -/
theorem effective_coefficient_error_budget :
    frameError*(7/25)*(1+2)+
      (frameError*(11/5)*3+2*(11/5)*correctorError) ≤ (1/10^6 : ℝ) := by
  norm_num [frameError, correctorError]

theorem quadratic_residual_error_budget :
    (7/25)*frameError+(11/5)*correctorError ≤ (1/10^6 : ℝ) := by
  norm_num [frameError, correctorError]

theorem rounded_coefficient_error_budget :
    (1/10^6 : ℝ)+3/10^11 ≤ 2/10^6 := by norm_num

end
end Maxwell.Certificate.OtherPointBudgets
