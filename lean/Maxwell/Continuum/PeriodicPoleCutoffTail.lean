import Maxwell.Continuum.PoleCutoffIntegral
import Maxwell.Continuum.PoleTailLedger
import Maxwell.Continuum.PeriodicPoleResidueAmplitude

/-! Uniform cutoff-tail estimate at the actual transverse Maxwell pole. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option exponentiation.threshold 8192
set_option maxRecDepth 2048

namespace Maxwell.Continuum.PeriodicBand

open FreeFiber Auxiliary Set Metric MeasureTheory TransverseGaussian OscillatoryPole

attribute [local irreducible] transversePole polePlanePhase selectedPoleAmplitude

theorem polePlanePhase_cutoff_small {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) {x : Plane}
    (hx : ‖x‖ ≤ 4*poleTransverseScale) :
    ‖polePlanePhase D hh j x‖ ≤ poleLongitudinalScale/2 := by
  have hw : ‖transverseMomentum j x‖ < transversePoleRadius :=
    (transverseMomentum_norm j x).trans_lt
      ((hx.trans poleCutoff_scales.2.2.2.2.2.1).trans_lt poleGaussianRadius_lt)
  have hp : ‖polePlanePhase D hh j x‖ ≤ (2 : ℝ)^122*‖transverseMomentum j x‖^2 := by
    unfold polePlanePhase
    exact transversePole_quadratic_bound D hh j hw
  calc
    _ ≤ (2 : ℝ)^122*‖transverseMomentum j x‖^2 := hp
    _ ≤ (2 : ℝ)^122*(4*poleTransverseScale)^2 := by
      gcongr
      exact (transverseMomentum_norm j x).trans hx
    _ ≤ _ := by norm_num [poleTransverseScale, poleLongitudinalScale]

theorem polePlanePhase_cutoff_im_pos {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) {x : Plane}
    (hx : ‖x‖ ≤ 4*poleTransverseScale) (hx0 : x ≠ 0) :
    0 < (polePlanePhase D hh j x).im := by
  have hd := polePlanePhase_damping D hh j (hx.trans poleCutoff_scales.2.2.2.2.2.1)
  have hn := norm_pos_iff.mpr hx0
  exact lt_of_lt_of_le (by positivity) hd

theorem selectedPoleAmplitude_cutoff_bound {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) {x : Plane}
    (hx : ‖x‖ ≤ 4*poleTransverseScale) :
    ‖selectedPoleAmplitude D hh j (transverseMomentum j x)‖ ≤ (2 : ℝ)^65 := by
  have hw : ‖transverseMomentum j x‖ < transversePoleRadius :=
    (transverseMomentum_norm j x).trans_lt
      ((hx.trans poleCutoff_scales.2.2.2.2.2.1).trans_lt poleGaussianRadius_lt)
  calc
    _ ≤ ‖selectedPoleAmplitude D hh j (transverseMomentum j x)-selectedPoleAmplitude D hh j 0‖+
        ‖selectedPoleAmplitude D hh j 0‖ := norm_le_norm_sub_add _ _
    _ ≤ (2 : ℝ)^192*‖transverseMomentum j x‖+(2 : ℝ)^64 :=
      add_le_add (selectedPoleAmplitude_variation D hh j hw) (selectedPoleAmplitude_zero_bound D hh j)
    _ ≤ (2 : ℝ)^192*(4*poleTransverseScale)+(2 : ℝ)^64 := by
      gcongr
      exact (transverseMomentum_norm j x).trans hx
    _ ≤ _ := by norm_num [poleTransverseScale]

theorem actualPole_cutoff_tail {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) {x : Plane}
    (hx : ‖x‖ ≤ 4*poleTransverseScale) (hx0 : x ≠ 0) {T : ℝ} (hT : 0 < T) :
    ‖cutoffPoleIntegral poleLongitudinalScale (polePlanePhase D hh j x) T-
      ((2*Real.pi : ℝ) : ℂ)*Complex.I*Complex.exp (Complex.I*polePlanePhase D hh j x*T)‖ ≤
        (2 : ℝ)^70002/T^16 := by
  have hb := cutoffPole_error_bound poleCutoff_scales.1
    (show poleLongitudinalScale ≤ 1 by norm_num [poleLongitudinalScale])
    (polePlanePhase_cutoff_im_pos D hh j hx hx0) (polePlanePhase_cutoff_small D hh j hx) hT 15
  exact hb.trans (div_le_div_of_nonneg_right (poleTail_l1_ledger (by omega : 16≤16)) (by positivity))

theorem actualPole_cutoff_amplitude_tail {h z : ℝ} (D : Calibration h z)
    (hh : h ≤ 1/(2 : ℝ)^1024) (j : Fin 3) {x : Plane}
    (hx : ‖x‖ ≤ 4*poleTransverseScale) (hx0 : x ≠ 0) {T : ℝ} (hT : 0 < T) :
    ‖selectedPoleAmplitude D hh j (transverseMomentum j x)*
      (cutoffPoleIntegral poleLongitudinalScale (polePlanePhase D hh j x) T-
      ((2*Real.pi : ℝ) : ℂ)*Complex.I*Complex.exp (Complex.I*polePlanePhase D hh j x*T))‖ ≤
        (2 : ℝ)^70067/T^16 := by
  rw [norm_mul]
  calc
    _ ≤ (2 : ℝ)^65*((2 : ℝ)^70002/T^16) :=
      mul_le_mul (selectedPoleAmplitude_cutoff_bound D hh j hx)
        (actualPole_cutoff_tail D hh j hx hx0 hT) (norm_nonneg _) (by positivity)
    _ = _ := by rw [← mul_div_assoc, ← pow_add]

#print axioms actualPole_cutoff_amplitude_tail

end Maxwell.Continuum.PeriodicBand
