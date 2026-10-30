import Maxwell.Continuum.PeriodicPoleResidueAmplitude

/-! The Gaussian asymptotic with all phase and source data instantiated
by the literal Maxwell band and its actual localized mode. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric MeasureTheory TransverseGaussian
open scoped Classical

attribute [local irreducible] imaginaryPole poleSlope transversePole selectedPoleAmplitude
  polePlanePhase poleGaussianHessian

def selectedGaussianDomain : Set Plane := closedBall 0 poleGaussianRadius

theorem selectedGaussianDomain_maps (j : Fin 3) :
    MapsTo (transverseMomentum j) selectedGaussianDomain (ball 0 transversePoleRadius) := by
  intro x hx
  rw [mem_ball, dist_zero_right]
  have hx' : ‖x‖ ≤ poleGaussianRadius := by simpa only [selectedGaussianDomain, mem_closedBall, dist_zero_right] using hx
  exact (transverseMomentum_norm j x).trans_lt (hx'.trans_lt poleGaussianRadius_lt)

theorem selectedGaussianAmplitude_continuousOn {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    ContinuousOn (fun x : Plane => selectedPoleAmplitude D hh j (transverseMomentum j x))
      selectedGaussianDomain :=
  (selectedPoleAmplitude_continuousOn D hh j).comp
    (transverseMomentum_continuous j).continuousOn (selectedGaussianDomain_maps j)

theorem selectedGaussianPhase_continuousOn {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) :
    ContinuousOn (polePlanePhase D hh j) selectedGaussianDomain := by
  unfold polePlanePhase
  exact (transversePole_analytic D hh j).continuousOn.comp
    (transverseMomentum_continuous j).continuousOn (selectedGaussianDomain_maps j)

def selectedGaussianData {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) : LocalData where
  domain := selectedGaussianDomain
  domain_measurable := measurableSet_closedBall
  radius := poleGaussianRadius
  radius_pos := poleGaussianRadius_pos
  ball_subset := ball_subset_closedBall
  amplitude := selectedGaussianDomain.piecewise
    (fun x => selectedPoleAmplitude D hh j (transverseMomentum j x)) (fun _ => 0)
  phase := selectedGaussianDomain.piecewise (polePlanePhase D hh j) (fun _ => 0)
  quadratic := diagonalQuadratic (poleGaussianHessian D hh j) (poleSlope D hh j)
  amplitude_measurable := (selectedGaussianAmplitude_continuousOn D hh j).measurable_piecewise
    continuous_const.continuousOn measurableSet_closedBall
  phase_measurable := (selectedGaussianPhase_continuousOn D hh j).measurable_piecewise
    continuous_const.continuousOn measurableSet_closedBall
  quadratic_measurable := by
    apply Continuous.measurable
    unfold diagonalQuadratic
    fun_prop
  center := selectedPoleAmplitude D hh j 0
  damping := (2 : ℝ)^(-256 : ℤ)
  damping_pos := by positivity
  lipschitz := (2 : ℝ)^192
  lipschitz_nonneg := by positivity
  cubic := (2 : ℝ)^246
  cubic_nonneg := by positivity
  amplitude_error := by
    intro x hx
    rw [piecewise_eq_of_mem selectedGaussianDomain _ _ hx]
    have hw : ‖transverseMomentum j x‖ < transversePoleRadius := by
      simpa only [mem_ball, dist_zero_right] using selectedGaussianDomain_maps j hx
    exact (selectedPoleAmplitude_variation D hh j hw).trans
      (mul_le_mul_of_nonneg_left (transverseMomentum_norm j x) (by positivity))
  phase_error := by
    intro x hx
    rw [piecewise_eq_of_mem selectedGaussianDomain _ _ hx]
    apply polePlanePhase_cubic D hh j
    have hx' : ‖x‖ ≤ poleGaussianRadius := by simpa only [selectedGaussianDomain, mem_closedBall, dist_zero_right] using hx
    exact hx'.trans_lt poleGaussianRadius_lt
  phase_damping := by
    intro x hx
    rw [piecewise_eq_of_mem selectedGaussianDomain _ _ hx]
    exact polePlanePhase_damping D hh j
      (by simpa only [selectedGaussianDomain, mem_closedBall, dist_zero_right] using hx)
  quadratic_damping := by
    intro x
    exact (mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ)^(-256 : ℤ) ≤ (2 : ℝ)^(-15 : ℤ))
      (sq_nonneg ‖x‖)).trans (poleGaussian_quadratic_lower D hh j x)

def selectedGaussianIntegral {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) (T : ℝ) : ℂ :=
  ∫ x in selectedGaussianDomain,
    selectedPoleAmplitude D hh j (transverseMomentum j x) * wave T (polePlanePhase D hh j x)

theorem selectedGaussian_asymptotic {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1 / (2 : ℝ)^1024) (j : Fin 3) {T : ℝ} (hT : 0 < T) :
    ‖selectedGaussianIntegral D hh j T - selectedPoleAmplitude D hh j 0 *
      ((2 * Real.pi * poleSlope D hh j /
        (T * Real.sqrt (poleGaussianHessian D hh j 0 * poleGaussianHessian D hh j 1)) : ℝ) : ℂ)‖ ≤
      (selectedGaussianData D hh j).errorConstant / (T * Real.sqrt T) := by
  have he := (selectedGaussianData D hh j).diagonal_asymptotic (poleGaussianHessian D hh j)
    (fun k => lt_trans (by positivity) (poleGaussianHessian_bounds D hh j k).1)
    hT (lt_trans (by norm_num) (poleSlope_bounds D hh j).1) rfl
  have hi : (∫ x in (selectedGaussianData D hh j).domain,
      (selectedGaussianData D hh j).amplitude x * wave T ((selectedGaussianData D hh j).phase x)) =
      selectedGaussianIntegral D hh j T := by
    apply setIntegral_congr_fun measurableSet_closedBall
    intro x hx
    simp only [selectedGaussianData, piecewise_eq_of_mem selectedGaussianDomain _ _ hx]
  rw [hi] at he
  exact he

#print axioms selectedGaussian_asymptotic

end Maxwell.Continuum.PeriodicBand
