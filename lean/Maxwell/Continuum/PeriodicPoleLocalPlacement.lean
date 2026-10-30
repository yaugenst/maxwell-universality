import Maxwell.Continuum.PeriodicPoleLocalIntegral
import Maxwell.Continuum.PeriodicPoleResidueContribution

/-! The actual cutoff local integral in the integer placement direction.
The leading coefficient and action are the previously constructed
physical quantities, now attached to the real integral itself. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric MeasureTheory TransverseGaussian

attribute [local irreducible] selectedGaussianCoefficient poleAction

def selectedLocalContribution {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) (d : ℝ) : ℂ :=
  (Real.exp (-poleAction D hh j*d) : ℂ)*selectedLocalIntegral D hh j (2*(placementDiagonal j : ℝ)*d)

theorem selectedLocalContribution_asymptotic {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) {d : ℝ} (hd : 1 ≤ d) :
    ‖selectedLocalContribution D hh j d-
      (Real.exp (-poleAction D hh j*d) : ℂ)*((selectedLeadingCoefficient D hh j/d : ℝ) : ℂ)‖ ≤
      (2 : ℝ)^70069*Real.exp (-poleAction D hh j*d)/(d*Real.sqrt d) := by
  have hd0 : 0 < d := lt_of_lt_of_le (by norm_num) hd
  let T : ℝ := 2*(placementDiagonal j : ℝ)*d
  have hTd : d ≤ T := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (placementDiagonal_residue_bounds j).1 hd0.le
  have hT : 0 < T := hd0.trans_le hTd
  have he := selectedLocalIntegral_asymptotic D hh j (hd.trans hTd)
  have hc : ((selectedGaussianCoefficient D hh j : ℝ) : ℂ)/(T : ℂ) =
      ((selectedLeadingCoefficient D hh j/d : ℝ) : ℂ) := by
    unfold selectedLeadingCoefficient
    dsimp only [T]
    push_cast
    ring
  rw [hc] at he
  unfold selectedLocalContribution
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hden : d*Real.sqrt d ≤ T*Real.sqrt T :=
    mul_le_mul hTd (Real.sqrt_le_sqrt hTd) (Real.sqrt_nonneg d) hT.le
  calc
    _ ≤ Real.exp (-poleAction D hh j*d)*((2 : ℝ)^70069/(T*Real.sqrt T)) :=
      mul_le_mul_of_nonneg_left he (Real.exp_pos _).le
    _ ≤ Real.exp (-poleAction D hh j*d)*((2 : ℝ)^70069/(d*Real.sqrt d)) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (by positivity) (by positivity) hden) (Real.exp_pos _).le
    _ = _ := by rw [← mul_div_assoc, mul_comm (Real.exp _) ((2 : ℝ)^70069)]

theorem selectedLocalContribution_master {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) {d : ℝ} (hd : 1 ≤ d) :
    ‖selectedLocalContribution D hh j d-
      (Real.exp (-poleAction D hh j*d) : ℂ)*((selectedLeadingCoefficient D hh j/d : ℝ) : ℂ)‖ ≤
      MasterConstants.Cs*Real.exp (-poleAction D hh j*d)/(d*Real.sqrt d) := by
  apply (selectedLocalContribution_asymptotic D hh j hd).trans
  apply div_le_div_of_nonneg_right
  · exact mul_le_mul_of_nonneg_right
      (MasterConstants.fixed_power_le_Cs (by norm_num [MasterConstants.exponent])) (Real.exp_pos _).le
  · exact mul_nonneg (le_trans (by norm_num) hd) (Real.sqrt_nonneg _)

#print axioms selectedLocalContribution_master
#print axioms selectedLeadingCoefficient_paper_lower

end Maxwell.Continuum.PeriodicBand
