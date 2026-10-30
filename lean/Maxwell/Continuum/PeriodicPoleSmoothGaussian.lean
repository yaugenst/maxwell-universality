import Maxwell.Continuum.PeriodicPoleGaussianCoefficient
import Maxwell.Continuum.PoleChartCutoff

/-! The transverse Gaussian asymptotic for the literal smooth local
cutoff, with the same actual positive leading residue coefficient. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 8192
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric MeasureTheory TransverseGaussian
open scoped Classical

attribute [local irreducible] imaginaryPole poleSlope transversePole selectedPoleAmplitude
  polePlanePhase poleGaussianHessian

theorem poleTransverseCutoff_continuous : Continuous poleTransverseCutoff := by
  unfold poleTransverseCutoff
  apply continuous_finsetProd
  intro k _
  exact (scaledPsi_contDiff poleTransverseScale).continuous.comp
    (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) k)

theorem poleTransverseCutoff_variation (x : Plane) :
    |poleTransverseCutoff x-1| ≤ ‖x‖/poleTransverseScale := by
  have ha := poleCutoff_scales.2.1
  by_cases hx : ‖x‖ ≤ poleTransverseScale
  · rw [poleTransverseCutoff_core hx, sub_self, abs_zero]
    positivity
  · rw [abs_of_nonpos (sub_nonpos.mpr (poleTransverseCutoff_le_one x)), neg_sub]
    exact (show 1-poleTransverseCutoff x ≤ 1 by linarith only [poleTransverseCutoff_nonneg x]).trans
      ((one_le_div ha).mpr (le_of_not_ge hx))

theorem selectedSmoothAmplitude_variation {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) {x : Plane} (hx : x ∈ selectedGaussianDomain) :
    ‖(poleTransverseCutoff x : ℂ)*selectedPoleAmplitude D hh j (transverseMomentum j x)-
      selectedPoleAmplitude D hh j 0‖ ≤ (2 : ℝ)^4166*‖x‖ := by
  have hw : ‖transverseMomentum j x‖ < transversePoleRadius := by
    simpa only [mem_ball, dist_zero_right] using selectedGaussianDomain_maps j hx
  have hv := (selectedPoleAmplitude_variation D hh j hw).trans
    (mul_le_mul_of_nonneg_left (transverseMomentum_norm j x) (by positivity))
  have hnonneg : 0 ≤ ‖x‖/poleTransverseScale :=
    div_nonneg (norm_nonneg x) poleCutoff_scales.2.1.le
  have he : (poleTransverseCutoff x : ℂ)*selectedPoleAmplitude D hh j (transverseMomentum j x)-
      selectedPoleAmplitude D hh j 0 =
      (poleTransverseCutoff x : ℂ)*(selectedPoleAmplitude D hh j (transverseMomentum j x)-
        selectedPoleAmplitude D hh j 0)+
        ((poleTransverseCutoff x-1 : ℝ) : ℂ)*selectedPoleAmplitude D hh j 0 := by push_cast; ring
  rw [he]
  calc
    _ ≤ ‖(poleTransverseCutoff x : ℂ)*(selectedPoleAmplitude D hh j (transverseMomentum j x)-
        selectedPoleAmplitude D hh j 0)‖+
        ‖((poleTransverseCutoff x-1 : ℝ) : ℂ)*selectedPoleAmplitude D hh j 0‖ := norm_add_le _ _
    _ ≤ (2 : ℝ)^192*‖x‖+(‖x‖/poleTransverseScale)*(2 : ℝ)^64 := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (poleTransverseCutoff_nonneg x)]
      exact add_le_add ((mul_le_of_le_one_left (norm_nonneg _) (poleTransverseCutoff_le_one x)).trans hv)
        (mul_le_mul (poleTransverseCutoff_variation x) (selectedPoleAmplitude_zero_bound D hh j)
          (norm_nonneg _) hnonneg)
    _ = ((2 : ℝ)^192+(2 : ℝ)^64/poleTransverseScale)*‖x‖ := by ring
    _ ≤ _ := by
      have hc : (2 : ℝ)^192+(2 : ℝ)^64/poleTransverseScale ≤ (2 : ℝ)^4166 := by
        norm_num [poleTransverseScale]
      exact mul_le_mul_of_nonneg_right hc (norm_nonneg x)

def selectedSmoothGaussianData {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) : LocalData :=
  { selectedGaussianData D hh j with
    amplitude := selectedGaussianDomain.piecewise
      (fun x => (poleTransverseCutoff x : ℂ)*selectedPoleAmplitude D hh j (transverseMomentum j x))
      (fun _ => 0)
    amplitude_measurable :=
      ((Complex.continuous_ofReal.comp poleTransverseCutoff_continuous).continuousOn.mul
        (selectedGaussianAmplitude_continuousOn D hh j)).measurable_piecewise
          continuous_const.continuousOn measurableSet_closedBall
    lipschitz := (2 : ℝ)^4166
    lipschitz_nonneg := by positivity
    amplitude_error := by
      intro x hx
      rw [piecewise_eq_of_mem selectedGaussianDomain _ _ hx]
      exact selectedSmoothAmplitude_variation D hh j hx }

def selectedSmoothGaussianIntegral {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) (T : ℝ) : ℂ :=
  ∫x in selectedGaussianDomain, (poleTransverseCutoff x : ℂ)*
    selectedPoleAmplitude D hh j (transverseMomentum j x)*wave T (polePlanePhase D hh j x)

theorem selectedSmoothGaussian_errorConstant {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) :
    (selectedSmoothGaussianData D hh j).errorConstant ≤ (2 : ℝ)^4600 := by
  change ((2 : ℝ)^4166+‖selectedPoleAmplitude D hh j 0‖/poleGaussianRadius)*
      (2*Real.pi/((2 : ℝ)^(-256 : ℤ)*Real.sqrt ((2 : ℝ)^(-256 : ℤ))))+
      ‖selectedPoleAmplitude D hh j 0‖*(2 : ℝ)^246*
      (32*Real.pi/(((2 : ℝ)^(-256 : ℤ))^2*Real.sqrt ((2 : ℝ)^(-256 : ℤ)))) ≤ _
  have hsq : Real.sqrt ((2 : ℝ)^(-256 : ℤ)) = (2 : ℝ)^(-128 : ℤ) := by
    rw [show (2 : ℝ)^(-256 : ℤ)=((2 : ℝ)^(-128 : ℤ))^2 by norm_num,
      Real.sqrt_sq (by positivity)]
  calc
    _ ≤ ((2 : ℝ)^4166+(2 : ℝ)^64/poleGaussianRadius)*
        (2*4/((2 : ℝ)^(-256 : ℤ)*Real.sqrt ((2 : ℝ)^(-256 : ℤ))))+
        (2 : ℝ)^64*(2 : ℝ)^246*
        (32*4/(((2 : ℝ)^(-256 : ℤ))^2*Real.sqrt ((2 : ℝ)^(-256 : ℤ)))) := by
      have hr := poleGaussianRadius_pos
      gcongr <;> first | exact selectedPoleAmplitude_zero_bound D hh j | exact Real.pi_lt_four.le
    _ ≤ _ := by rw [hsq]; norm_num [poleGaussianRadius]

theorem selectedSmoothGaussian_asymptotic {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) {T : ℝ} (hT : 0 < T) :
    ‖selectedSmoothGaussianIntegral D hh j T-selectedPoleAmplitude D hh j 0*
      ((2*Real.pi*poleSlope D hh j/
        (T*Real.sqrt (poleGaussianHessian D hh j 0*poleGaussianHessian D hh j 1)) : ℝ) : ℂ)‖ ≤
      (2 : ℝ)^4600/(T*Real.sqrt T) := by
  have he := (selectedSmoothGaussianData D hh j).diagonal_asymptotic (poleGaussianHessian D hh j)
    (fun k => lt_trans (by positivity) (poleGaussianHessian_bounds D hh j k).1)
    hT (lt_trans (by norm_num) (poleSlope_bounds D hh j).1) rfl
  have hi : (∫x in (selectedSmoothGaussianData D hh j).domain,
      (selectedSmoothGaussianData D hh j).amplitude x*wave T ((selectedSmoothGaussianData D hh j).phase x)) =
      selectedSmoothGaussianIntegral D hh j T := by
    apply setIntegral_congr_fun measurableSet_closedBall
    intro x hx
    simp only [selectedSmoothGaussianData, selectedGaussianData,
      piecewise_eq_of_mem selectedGaussianDomain _ _ hx]
  rw [hi] at he
  exact he.trans (div_le_div_of_nonneg_right (selectedSmoothGaussian_errorConstant D hh j) (by positivity))

theorem selectedSmoothGaussian_residue_asymptotic {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) {T : ℝ} (hT : 0 < T) :
    ‖(((2*Real.pi : ℝ) : ℂ)*Complex.I)*selectedSmoothGaussianIntegral D hh j T-
      ((selectedGaussianCoefficient D hh j : ℝ) : ℂ)/(T : ℂ)‖ ≤
      (2 : ℝ)^4603/(T*Real.sqrt T) := by
  rw [← selectedGaussian_residue_coefficient D hh j T, ← mul_sub, norm_mul]
  have hf : ‖(((2*Real.pi : ℝ) : ℂ)*Complex.I)‖ ≤ 8 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), Complex.norm_I, mul_one]
    linarith only [Real.pi_lt_four]
  calc
    _ ≤ 8*((2 : ℝ)^4600/(T*Real.sqrt T)) :=
      mul_le_mul hf (selectedSmoothGaussian_asymptotic D hh j hT) (norm_nonneg _) (by norm_num)
    _ = _ := by rw [← mul_div_assoc, show (8 : ℝ)=2^3 by norm_num, ← pow_add]

#print axioms selectedSmoothGaussian_asymptotic
#print axioms selectedSmoothGaussian_residue_asymptotic

end Maxwell.Continuum.PeriodicBand
