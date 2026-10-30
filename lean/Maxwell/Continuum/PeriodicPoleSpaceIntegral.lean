import Maxwell.Continuum.PeriodicPoleLocalCutoff
import Maxwell.Continuum.PeriodicPoleLocalPlacement
import Maxwell.Continuum.PeriodicSelectedSplit

/-! The actual local selected symbol in physical three-dimensional
coordinates, joined to the proved longitudinal residue and Gaussian
asymptotic by a measure-preserving change of variables. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric MeasureTheory TransverseGaussian OscillatoryPole

attribute [local irreducible] selectedPoleNumerator poleDenominator selectedGaussianCoefficient

theorem localSelectedSymbol_eq_quotient {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) (k : Space) :
    localSelectedSymbol D hh j k = (poleChartCutoff j k : ℂ)*
      selectedGlobalQuotient D hh j (realMomentum k.ofLp) := by
  change (poleChartCutoff j k : ℂ)*(scaledPoleCutoff D hh j k*
    selectedGlobalQuotient D hh j (realMomentum k.ofLp)) = _
  by_cases hk : poleChartCutoff j k = 0
  · simp only [hk, Complex.ofReal_zero, zero_mul]
  · rw [scaledPoleCutoff_eq_one_local D hh hk, one_mul]

theorem localSelectedSymbol_coordinates {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) (x : Plane) (T u : ℝ) :
    oscillatoryPhase T (poleCoordinateSpace j x u j)*
      localSelectedSymbol D hh j (poleCoordinateSpace j x u) =
    (poleTransverseCutoff x : ℂ)*selectedLongitudinalIntegrand D hh j x T u := by
  rw [localSelectedSymbol_eq_quotient, poleCoordinateSpace_cutoff,
    poleCoordinateSpace_realMomentum, poleCoordinateSpace_same]
  unfold selectedLongitudinalIntegrand selectedGlobalQuotient realPoleCoordinates complexCutoff
  push_cast
  ring

theorem selectedLocalSpaceIntegrable {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) (T : ℝ) :
    Integrable (fun k : Space => oscillatoryPhase T (k j)*localSelectedSymbol D hh j k) := by
  apply (localSelectedSymbol_integrable D hh j).bdd_mul
  · exact (show Continuous (fun k : Space => oscillatoryPhase T (k j)) by
      unfold oscillatoryPhase
      fun_prop).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun k => (oscillatoryPhase_norm T (k j)).le)

theorem selectedLocalSpaceIntegral_eq {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) (T : ℝ) :
    (∫k : Space, oscillatoryPhase T (k j)*localSelectedSymbol D hh j k) =
      selectedLocalIntegral D hh j T := by
  rw [poleSpace_integral j _ (selectedLocalSpaceIntegrable D hh j T)]
  simp_rw [localSelectedSymbol_coordinates, integral_const_mul]
  unfold selectedLocalIntegral selectedLongitudinalIntegral
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
  intro x hx
  have hz : poleTransverseCutoff x = 0 := by
    by_contra hn
    apply hx
    change ‖x-0‖ ≤ poleGaussianRadius
    simpa only [sub_zero] using
      (poleTransverseCutoff_support hn).trans poleCutoff_scales.2.2.2.2.2.1
  rw [hz, Complex.ofReal_zero, zero_mul]

theorem selectedLocalSpaceIntegral_asymptotic {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) {T : ℝ} (hT : 1 ≤ T) :
    ‖(∫k : Space, oscillatoryPhase T (k j)*localSelectedSymbol D hh j k)-
      ((selectedGaussianCoefficient D hh j : ℝ) : ℂ)/(T : ℂ)‖ ≤
      (2 : ℝ)^70069/(T*Real.sqrt T) := by
  rw [selectedLocalSpaceIntegral_eq]
  exact selectedLocalIntegral_asymptotic D hh j hT

theorem selectedLocalSpaceIntegral_placement {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) {d : ℝ} (hd : 1 ≤ d) :
    ‖(Real.exp (-poleAction D hh j*d) : ℂ)*
        (∫k : Space, oscillatoryPhase (2*(placementDiagonal j : ℝ)*d) (k j)*localSelectedSymbol D hh j k)-
      (Real.exp (-poleAction D hh j*d) : ℂ)*((selectedLeadingCoefficient D hh j/d : ℝ) : ℂ)‖ ≤
      (2 : ℝ)^70069*Real.exp (-poleAction D hh j*d)/(d*Real.sqrt d) := by
  rw [selectedLocalSpaceIntegral_eq]
  exact selectedLocalContribution_asymptotic D hh j hd

#print axioms selectedLocalSpaceIntegral_eq
#print axioms selectedLocalSpaceIntegral_placement

end Maxwell.Continuum.PeriodicBand
