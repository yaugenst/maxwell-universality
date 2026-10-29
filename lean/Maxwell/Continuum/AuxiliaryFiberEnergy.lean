import Maxwell.Continuum.AuxiliaryEnergy
import Maxwell.Continuum.PeriodicBandRealResolvent

/-! The calibrated physical energy lies in the literal isolated-band
resolvent window for every real momentum on the cutoff support. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Auxiliary

open FreeFiber PeriodicBand FiberAnalytic Metric

def sampledEnergy (z σ : ℝ) : ℂ := ((z + σ + 7 : ℝ) : ℂ)

def fiberParameter (q : Corner.Vec) : Momentum := unscale (realMomentum q)

def sampledScaledEnergy (z σ : ℝ) : ℂ := scaledEnergy (sampledEnergy z σ)

theorem fiberParameter_real (q : Corner.Vec) :
    fiberParameter q = realMomentum (fun j => q j / backgroundAmplitude) := by
  funext j
  simp only [fiberParameter, unscale, realMomentum, Pi.smul_apply, smul_eq_mul,
    div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv]
  ring

theorem fiberParameter_chart (q : Corner.Vec)
    (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) : fiberParameter q ∈ chart :=
  unscale_mem_chart (small_momentum_mem_physicalChart hq)

theorem sampledEnergy_band_distance {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) :
    ‖sampledEnergy z σ - physicalBand (fiberParameter q)‖ =
      (dielectricBand (realMomentum q)).re - (z + σ) := by
  have hb := (calibration_denominator_bounds D hσ0 hσ q hq).1
  have hr := dielectricBand_ofReal_re q (small_momentum_mem_physicalChart hq)
  have heq : sampledEnergy z σ - physicalBand (fiberParameter q) =
      ((z + σ - (dielectricBand (realMomentum q)).re : ℝ) : ℂ) := by
    push_cast
    rw [hr]
    unfold sampledEnergy fiberParameter dielectricBand
    push_cast
    ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos]
  · ring
  · nlinarith [sq_nonneg h]

theorem sampledEnergy_distance_bounds {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) :
    h ^ 2 / 2 ≤ ‖sampledEnergy z σ - physicalBand (fiberParameter q)‖ ∧
      ‖sampledEnergy z σ - physicalBand (fiberParameter q)‖ ≤ backgroundAmplitude / 200 := by
  rw [sampledEnergy_band_distance D hσ0 hσ q hq]
  exact calibration_denominator_bounds D hσ0 hσ q hq

theorem sampledEnergy_ne_band {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) :
    sampledEnergy z σ ≠ physicalBand (fiberParameter q) := by
  intro heq
  have h := (sampledEnergy_distance_bounds D hσ0 hσ q hq).1
  rw [heq, sub_self, norm_zero] at h
  nlinarith [sq_pos_of_pos D.h_pos]

theorem sampledScaledEnergy_mem {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) :
    sampledScaledEnergy z σ ∈ closedBall (scaledBand (fiberParameter q)) (1 / 200) := by
  have he := (sampledEnergy_distance_bounds D hσ0 hσ q hq).2
  have hid := totalEnergy_sub_norm (sampledScaledEnergy z σ) (scaledBand (fiberParameter q))
  rw [sampledScaledEnergy, totalEnergy_scaledEnergy] at hid
  change ‖sampledEnergy z σ - totalEnergy (scaledBand (fiberParameter q))‖ ≤ _ at he
  rw [hid] at he
  rw [mem_closedBall, dist_eq_norm]
  change ‖scaledEnergy (sampledEnergy z σ) - scaledBand (fiberParameter q)‖ ≤ _
  nlinarith [backgroundAmplitude_pos]

theorem sampledScaledEnergy_ne_band {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64)
    (q : Corner.Vec) (hq : ‖realMomentum q‖ ≤ 4 * smallRadius) :
    sampledScaledEnergy z σ ≠ scaledBand (fiberParameter q) :=
  scaledEnergy_ne_band (sampledEnergy_ne_band D hσ0 hσ q hq)

end Maxwell.Continuum.Auxiliary
