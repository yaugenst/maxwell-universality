import Maxwell.Continuum.PeriodicPoleLongitudinalIntegral
import Maxwell.Continuum.PeriodicPoleSmoothGaussian
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! Measurability of the literal local quotient and its longitudinal
integral. Only values inside the proved analytic chart are used. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 8192
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric MeasureTheory TransverseGaussian OscillatoryPole
open scoped Classical

def selectedLocalNumerator {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) : Momentum → ℂ :=
  (closedBall 0 (1/8 : ℝ)).piecewise (selectedPoleNumerator D hh j) (fun _ => 0)

def selectedLocalDenominator {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) : Momentum → ℂ :=
  (closedBall 0 (1/8 : ℝ)).piecewise (poleDenominator D hh j) (fun _ => 0)

theorem selectedLocalNumerator_measurable {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) : Measurable (selectedLocalNumerator D hh j) :=
  (selectedPoleNumerator_lipschitz D hh j).continuousOn.measurable_piecewise
    continuous_const.continuousOn measurableSet_closedBall

theorem selectedLocalDenominator_measurable {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) : Measurable (selectedLocalDenominator D hh j) :=
  ((poleDenominator_analytic D hh j).continuousOn.mono
    (closedBall_subset_ball (by norm_num : (1/8 : ℝ)<1))).measurable_piecewise
      continuous_const.continuousOn measurableSet_closedBall

def realPoleCoordinates (j : Fin 3) (y : Plane × ℝ) : Momentum :=
  poleOffset j (transverseMomentum j y.1) (y.2 : ℂ)

theorem realPoleCoordinates_continuous (j : Fin 3) : Continuous (realPoleCoordinates j) := by
  apply continuous_pi
  intro k
  by_cases hk : k = j
  · subst k
    simp only [realPoleCoordinates, poleOffset_same]
    convert! Complex.continuous_ofReal.comp (continuous_snd : Continuous (Prod.snd : Plane × ℝ → ℝ)) using 1
  · simp only [realPoleCoordinates, poleOffset_other j k hk]
    convert! (continuous_apply k).comp ((transverseMomentum_continuous j).comp
      (continuous_fst : Continuous (Prod.fst : Plane × ℝ → Plane))) using 1

theorem realPoleCoordinates_small (j : Fin 3) {x : Plane} {u : ℝ}
    (hx : poleTransverseCutoff x ≠ 0) (hu : complexCutoff poleLongitudinalScale u ≠ 0) :
    realPoleCoordinates j (x,u) ∈ closedBall 0 (1/8 : ℝ) := by
  have hx' := poleTransverseCutoff_support hx
  have hu' : |u| ≤ 2*poleLongitudinalScale := by
    have hc : scaledPsi poleLongitudinalScale u ≠ 0 := fun he => hu (by rw [complexCutoff, he, Complex.ofReal_zero])
    have hs := scaledPsi_support poleCutoff_scales.1 hc
    exact abs_le.mpr ⟨by linarith only [hs.1], hs.2⟩
  rw [mem_closedBall, dist_zero_right]
  apply poleOffset_norm_le (by norm_num) j
  · exact ((transverseMomentum_norm j x).trans hx').trans
      (by norm_num [poleTransverseScale])
  · rw [Complex.norm_real, Real.norm_eq_abs]
    exact hu'.trans (by norm_num [poleLongitudinalScale])

theorem selectedLocalIntegrand_eq {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) (T : ℝ) (x : Plane) (u : ℝ) :
    (poleTransverseCutoff x : ℂ)*selectedLongitudinalIntegrand D hh j x T u =
      (poleTransverseCutoff x : ℂ)*(oscillatoryPhase T u*complexCutoff poleLongitudinalScale u)*
        (selectedLocalNumerator D hh j (realPoleCoordinates j (x,u))/
          selectedLocalDenominator D hh j (realPoleCoordinates j (x,u))) := by
  by_cases hx : poleTransverseCutoff x = 0
  · simp only [hx, Complex.ofReal_zero, zero_mul]
  by_cases hu : complexCutoff poleLongitudinalScale u = 0
  · simp only [selectedLongitudinalIntegrand, hu, mul_zero, zero_mul]
  have hm := realPoleCoordinates_small j hx hu
  rw [selectedLocalNumerator, selectedLocalDenominator,
    piecewise_eq_of_mem _ _ _ hm, piecewise_eq_of_mem _ _ _ hm]
  unfold selectedLongitudinalIntegrand realPoleCoordinates
  ring

theorem selectedLocalIntegrand_measurable {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) (T : ℝ) :
    Measurable (fun y : Plane × ℝ =>
      (poleTransverseCutoff y.1 : ℂ)*selectedLongitudinalIntegrand D hh j y.1 T y.2) := by
  simp_rw [selectedLocalIntegrand_eq D hh j T]
  apply Measurable.mul
  · apply Measurable.mul
    · exact (Complex.continuous_ofReal.comp (poleTransverseCutoff_continuous.comp continuous_fst)).measurable
    · exact ((show Continuous (oscillatoryPhase T) from continuous_iff_continuousAt.mpr
        (fun u => (oscillatoryPhase_hasDerivAt T u).continuousAt)).measurable.comp measurable_snd).mul
          ((complexCutoff_contDiff poleLongitudinalScale).continuous.measurable.comp measurable_snd)
  · exact ((selectedLocalNumerator_measurable D hh j).comp (realPoleCoordinates_continuous j).measurable).div
      ((selectedLocalDenominator_measurable D hh j).comp (realPoleCoordinates_continuous j).measurable)

theorem selectedWeightedLongitudinal_measurable {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) (T : ℝ) :
    Measurable (fun x : Plane => (poleTransverseCutoff x : ℂ)*selectedLongitudinalIntegral D hh j x T) := by
  have he := (selectedLocalIntegrand_measurable D hh j T).stronglyMeasurable.integral_prod_right' (ν := volume)
  simpa only [integral_const_mul, selectedLongitudinalIntegral] using he.measurable

theorem selectedGaussianDomain_measure_le_one : volume.real selectedGaussianDomain ≤ 1 := by
  rw [Measure.real, selectedGaussianDomain, EuclideanSpace.volume_closedBall_fin_two,
    ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal poleGaussianRadius_pos.le, ENNReal.toReal_ofReal Real.pi_pos.le]
  calc
    _ ≤ poleGaussianRadius^2*4 := mul_le_mul_of_nonneg_left Real.pi_lt_four.le (sq_nonneg _)
    _ ≤ _ := by norm_num [poleGaussianRadius]

#print axioms selectedWeightedLongitudinal_measurable

end Maxwell.Continuum.PeriodicBand
