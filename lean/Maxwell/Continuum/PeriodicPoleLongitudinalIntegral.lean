import Maxwell.Continuum.PeriodicPoleRegularCutoff
import Maxwell.Continuum.PeriodicPoleCutoffTail

/-! The literal local Maxwell quotient integrated along the real
longitudinal line: residue plus a uniform sixteenth-order remainder. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 4096
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric MeasureTheory TransverseGaussian OscillatoryPole

attribute [local irreducible] selectedPoleNumerator poleDenominator selectedRegularPart
  selectedPoleAmplitude transversePole

def selectedLongitudinalIntegrand {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) (x : Plane) (T u : ℝ) : ℂ :=
  oscillatoryPhase T u*complexCutoff poleLongitudinalScale u*
    (selectedPoleNumerator D hh j (poleOffset j (transverseMomentum j x) (u : ℂ))/
      poleDenominator D hh j (poleOffset j (transverseMomentum j x) (u : ℂ)))

def selectedLongitudinalIntegral {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) (x : Plane) (T : ℝ) : ℂ :=
  ∫u : ℝ, selectedLongitudinalIntegrand D hh j x T u

theorem selectedLongitudinalIntegrand_split {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) {x : Plane}
    (hx : ‖x‖ ≤ 4*poleTransverseScale) (hx0 : x ≠ 0) (T u : ℝ) :
    selectedLongitudinalIntegrand D hh j x T u =
      selectedPoleAmplitude D hh j (transverseMomentum j x)*
        (oscillatoryPhase T u*(complexCutoff poleLongitudinalScale u*poleSimple (polePlanePhase D hh j x) u))+
      oscillatoryPhase T u*cutoffHolomorphic poleLongitudinalScale
        (selectedRegularPart D hh j (transverseMomentum j x)) u := by
  have hw : ‖transverseMomentum j x‖ < transversePoleRadius :=
    (transverseMomentum_norm j x).trans_lt
      ((hx.trans poleCutoff_scales.2.2.2.2.2.1).trans_lt poleGaussianRadius_lt)
  by_cases hu : |u| ≤ 2*poleLongitudinalScale
  · have huc : ‖(u : ℂ)‖ ≤ longitudinalPoleRadius := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hu.trans (regularCutoff_radius.le.trans (by linarith only [pole_radii.1]))
    have hne : (u : ℂ) ≠ transversePole D hh j (transverseMomentum j x) := by
      exact sub_ne_zero.mp (real_sub_pole_ne_zero (polePlanePhase_cutoff_im_pos D hh j hx hx0) u)
    have he := selectedPole_exact_division D hh j hw huc hne
    unfold selectedLongitudinalIntegrand
    rw [he]
    unfold cutoffHolomorphic poleSimple polePlanePhase
    ring
  · have hz : complexCutoff poleLongitudinalScale u = 0 := by
      rw [complexCutoff, scaledPsi_eq_zero poleCutoff_scales.1 (le_of_not_ge hu), Complex.ofReal_zero]
    simp only [selectedLongitudinalIntegrand, cutoffHolomorphic, hz, mul_zero, zero_mul, add_zero]

theorem selectedLongitudinalIntegral_split {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) {x : Plane}
    (hx : ‖x‖ ≤ 4*poleTransverseScale) (hx0 : x ≠ 0) (T : ℝ) :
    selectedLongitudinalIntegral D hh j x T =
      selectedPoleAmplitude D hh j (transverseMomentum j x)*
        cutoffPoleIntegral poleLongitudinalScale (polePlanePhase D hh j x) T+
      ∫u : ℝ, oscillatoryPhase T u*cutoffHolomorphic poleLongitudinalScale
        (selectedRegularPart D hh j (transverseMomentum j x)) u := by
  have hw : ‖transverseMomentum j x‖ < transversePoleRadius :=
    (transverseMomentum_norm j x).trans_lt
      ((hx.trans poleCutoff_scales.2.2.2.2.2.1).trans_lt poleGaussianRadius_lt)
  have hi1 := (phase_mul_integrable (cutoffPole_integrable poleCutoff_scales.1
    (polePlanePhase_cutoff_im_pos D hh j hx hx0)) T).const_mul
      (selectedPoleAmplitude D hh j (transverseMomentum j x))
  have hi2 : Integrable (fun u : ℝ => oscillatoryPhase T u*cutoffHolomorphic poleLongitudinalScale
      (selectedRegularPart D hh j (transverseMomentum j x)) u) := by
    apply phase_mul_integrable
    simpa only [iteratedDeriv_zero] using cutoffHolomorphic_jet_integrable poleCutoff_scales.1
      regularCutoff_radius (selectedRegularCutoff_analytic D hh j hw) 0
  unfold selectedLongitudinalIntegral
  simp_rw [selectedLongitudinalIntegrand_split D hh j hx hx0]
  rw [integral_add hi1 hi2, integral_const_mul]
  rfl

theorem selectedLongitudinalIntegral_residue {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) {x : Plane}
    (hx : ‖x‖ ≤ 4*poleTransverseScale) (hx0 : x ≠ 0) {T : ℝ} (hT : 0 < T) :
    ‖selectedLongitudinalIntegral D hh j x T-
      ((2*Real.pi : ℝ) : ℂ)*Complex.I*selectedPoleAmplitude D hh j (transverseMomentum j x)*
        wave T (polePlanePhase D hh j x)‖ ≤ (2 : ℝ)^70068/T^16 := by
  have hw : ‖transverseMomentum j x‖ < transversePoleRadius :=
    (transverseMomentum_norm j x).trans_lt
      ((hx.trans poleCutoff_scales.2.2.2.2.2.1).trans_lt poleGaussianRadius_lt)
  rw [selectedLongitudinalIntegral_split D hh j hx hx0]
  have hphase : wave T (polePlanePhase D hh j x) =
      Complex.exp (Complex.I*polePlanePhase D hh j x*T) := by
    unfold wave
    congr 1
    ring
  rw [hphase]
  have he : selectedPoleAmplitude D hh j (transverseMomentum j x)*
      cutoffPoleIntegral poleLongitudinalScale (polePlanePhase D hh j x) T+
      (∫u : ℝ, oscillatoryPhase T u*cutoffHolomorphic poleLongitudinalScale
        (selectedRegularPart D hh j (transverseMomentum j x)) u)-
      ((2*Real.pi : ℝ) : ℂ)*Complex.I*selectedPoleAmplitude D hh j (transverseMomentum j x)*
        Complex.exp (Complex.I*polePlanePhase D hh j x*T) =
      selectedPoleAmplitude D hh j (transverseMomentum j x)*
        (cutoffPoleIntegral poleLongitudinalScale (polePlanePhase D hh j x) T-
          ((2*Real.pi : ℝ) : ℂ)*Complex.I*Complex.exp (Complex.I*polePlanePhase D hh j x*T))+
      (∫u : ℝ, oscillatoryPhase T u*cutoffHolomorphic poleLongitudinalScale
        (selectedRegularPart D hh j (transverseMomentum j x)) u) := by ring
  rw [he]
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ (2 : ℝ)^70067/T^16+(2 : ℝ)^51002/T^16 :=
      add_le_add (actualPole_cutoff_amplitude_tail D hh j hx hx0 hT)
        (selectedRegularCutoff_oscillatory_bound D hh j hw hT)
    _ ≤ (2 : ℝ)^70067/T^16+(2 : ℝ)^70067/T^16 := by
      have hp : (2 : ℝ)^51002 ≤ (2 : ℝ)^70067 :=
        pow_le_pow_right₀ (by norm_num) (by norm_num)
      have hq : (2 : ℝ)^51002/T^16 ≤ (2 : ℝ)^70067/T^16 :=
        div_le_div_of_nonneg_right hp (pow_nonneg hT.le 16)
      exact add_le_add (le_refl ((2 : ℝ)^70067/T^16)) hq
    _ = _ := by
      rw [← add_div, ← two_mul, pow_succ (2 : ℝ) 70067, mul_comm ((2 : ℝ)^70067) 2]

#print axioms selectedLongitudinalIntegral_residue

end Maxwell.Continuum.PeriodicBand
