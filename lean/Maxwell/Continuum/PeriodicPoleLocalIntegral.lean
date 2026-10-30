import Maxwell.Continuum.PeriodicPoleLocalMeasurable

/-! The local three-dimensional selected-band integral, with the
longitudinal residue and the smooth transverse Gaussian estimate joined. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric MeasureTheory TransverseGaussian OscillatoryPole

def selectedLocalIntegral {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) (T : ℝ) : ℂ :=
  ∫x in selectedGaussianDomain, (poleTransverseCutoff x : ℂ)*selectedLongitudinalIntegral D hh j x T

def selectedLocalResidue {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) (T : ℝ) (x : Plane) : ℂ :=
  ((2*Real.pi : ℝ) : ℂ)*Complex.I*(poleTransverseCutoff x : ℂ)*
    selectedPoleAmplitude D hh j (transverseMomentum j x)*wave T (polePlanePhase D hh j x)

theorem selectedLocalResidue_continuousOn {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) (T : ℝ) :
    ContinuousOn (selectedLocalResidue D hh j T) selectedGaussianDomain := by
  have hc : ContinuousOn (fun x : Plane => (poleTransverseCutoff x : ℂ)) selectedGaussianDomain :=
    (Complex.continuous_ofReal.comp poleTransverseCutoff_continuous).continuousOn
  have hw : Continuous (wave T) := by unfold wave; fun_prop
  exact ((continuousOn_const.mul hc).mul (selectedGaussianAmplitude_continuousOn D hh j)).mul
    (hw.comp_continuousOn (selectedGaussianPhase_continuousOn D hh j))

theorem selectedLocalResidue_integrableOn {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) (T : ℝ) :
    IntegrableOn (selectedLocalResidue D hh j T) selectedGaussianDomain :=
  (selectedLocalResidue_continuousOn D hh j T).integrableOn_compact (isCompact_closedBall _ _)

theorem selectedLocalError_ae {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) {T : ℝ} (hT : 0 < T) :
    ∀ᵐx : Plane, ‖(poleTransverseCutoff x : ℂ)*selectedLongitudinalIntegral D hh j x T-
      selectedLocalResidue D hh j T x‖ ≤ (2 : ℝ)^70068/T^16 := by
  filter_upwards [volume.ae_ne (0 : Plane)] with x hx0
  by_cases hx : poleTransverseCutoff x = 0
  · simp only [hx, selectedLocalResidue, Complex.ofReal_zero, mul_zero, zero_mul, sub_self, norm_zero]
    positivity
  · have he : (poleTransverseCutoff x : ℂ)*selectedLongitudinalIntegral D hh j x T-
        selectedLocalResidue D hh j T x =
        (poleTransverseCutoff x : ℂ)*(selectedLongitudinalIntegral D hh j x T-
          ((2*Real.pi : ℝ) : ℂ)*Complex.I*selectedPoleAmplitude D hh j (transverseMomentum j x)*
            wave T (polePlanePhase D hh j x)) := by unfold selectedLocalResidue; ring
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (poleTransverseCutoff_nonneg x)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (poleTransverseCutoff_le_one x)).trans
      (selectedLongitudinalIntegral_residue D hh j (poleTransverseCutoff_support hx) hx0 hT)

theorem selectedLocalIntegrable {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun x : Plane => (poleTransverseCutoff x : ℂ)*selectedLongitudinalIntegral D hh j x T)
      selectedGaussianDomain := by
  let : IsFiniteMeasure (volume.restrict selectedGaussianDomain) :=
    ⟨by simpa only [Measure.restrict_apply_univ, selectedGaussianDomain] using (isCompact_closedBall 0 poleGaussianRadius : IsCompact selectedGaussianDomain).measure_lt_top⟩
  have hg := selectedLocalResidue_integrableOn D hh j T
  have hm : AEStronglyMeasurable (fun x : Plane =>
      (poleTransverseCutoff x : ℂ)*selectedLongitudinalIntegral D hh j x T)
      (volume.restrict selectedGaussianDomain) :=
    (selectedWeightedLongitudinal_measurable D hh j T).aestronglyMeasurable
  have he : IntegrableOn (fun x : Plane =>
      (poleTransverseCutoff x : ℂ)*selectedLongitudinalIntegral D hh j x T-selectedLocalResidue D hh j T x)
      selectedGaussianDomain := by
    apply (integrable_const ((2 : ℝ)^70068/T^16)).mono' (hm.sub hg.aestronglyMeasurable)
    exact ae_restrict_of_ae (selectedLocalError_ae D hh j hT)
  convert he.add hg using 1
  funext x
  exact (sub_add_cancel _ _).symm

theorem selectedLocalIntegral_residue {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) {T : ℝ} (hT : 0 < T) :
    ‖selectedLocalIntegral D hh j T-
      (((2*Real.pi : ℝ) : ℂ)*Complex.I)*selectedSmoothGaussianIntegral D hh j T‖ ≤
      (2 : ℝ)^70068/T^16 := by
  let : IsFiniteMeasure (volume.restrict selectedGaussianDomain) :=
    ⟨by simpa only [Measure.restrict_apply_univ, selectedGaussianDomain] using (isCompact_closedBall 0 poleGaussianRadius : IsCompact selectedGaussianDomain).measure_lt_top⟩
  have hi : (∫x in selectedGaussianDomain, selectedLocalResidue D hh j T x) =
      (((2*Real.pi : ℝ) : ℂ)*Complex.I)*selectedSmoothGaussianIntegral D hh j T := by
    rw [selectedSmoothGaussianIntegral, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_closedBall
    intro x _
    unfold selectedLocalResidue
    ring
  rw [← hi, selectedLocalIntegral, ← integral_sub (selectedLocalIntegrable D hh j hT)
    (selectedLocalResidue_integrableOn D hh j T)]
  have hb := norm_integral_le_of_norm_le_const (μ := volume.restrict selectedGaussianDomain)
    (ae_restrict_of_ae (selectedLocalError_ae D hh j hT))
  simp only [Measure.real, Measure.restrict_apply_univ] at hb
  exact hb.trans (mul_le_of_le_one_right (by positivity)
    selectedGaussianDomain_measure_le_one)

theorem selectedLocalIntegral_asymptotic {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) {T : ℝ} (hT : 1 ≤ T) :
    ‖selectedLocalIntegral D hh j T-((selectedGaussianCoefficient D hh j : ℝ) : ℂ)/(T : ℂ)‖ ≤
      (2 : ℝ)^70069/(T*Real.sqrt T) := by
  have hT0 : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hden : T*Real.sqrt T ≤ T^16 := by
    calc
      _ ≤ T*T := mul_le_mul_of_nonneg_left
        (Real.sqrt_le_iff.mpr ⟨hT0.le, by nlinarith only [hT]⟩) hT0.le
      _ = T^2 := (pow_two T).symm
      _ ≤ T^16 := pow_le_pow_right₀ hT (by norm_num)
  calc
    _ ≤ ‖selectedLocalIntegral D hh j T-
        (((2*Real.pi : ℝ) : ℂ)*Complex.I)*selectedSmoothGaussianIntegral D hh j T‖+
        ‖(((2*Real.pi : ℝ) : ℂ)*Complex.I)*selectedSmoothGaussianIntegral D hh j T-
          ((selectedGaussianCoefficient D hh j : ℝ) : ℂ)/(T : ℂ)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (2 : ℝ)^70068/T^16+(2 : ℝ)^4603/(T*Real.sqrt T) :=
      add_le_add (selectedLocalIntegral_residue D hh j hT0) (selectedSmoothGaussian_residue_asymptotic D hh j hT0)
    _ ≤ (2 : ℝ)^70068/(T*Real.sqrt T)+(2 : ℝ)^70068/(T*Real.sqrt T) := by
      apply add_le_add
      · exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden
      · have hp : (2 : ℝ)^4603 ≤ (2 : ℝ)^70068 := pow_le_pow_right₀ (by norm_num) (by norm_num)
        exact div_le_div_of_nonneg_right hp (by positivity)
    _ = _ := by rw [← add_div, ← two_mul, pow_succ (2 : ℝ) 70068, mul_comm ((2 : ℝ)^70068) 2]

#print axioms selectedLocalIntegral_asymptotic

end Maxwell.Continuum.PeriodicBand
