import Maxwell.Continuum.PeriodicBandSeparatedJoint
import Maxwell.Continuum.AuxiliaryFiberEnergy
import Maxwell.Continuum.PeriodicBandComparison
import Maxwell.Continuum.CauchyMapLipschitz

/-! A fixed complex neighborhood for the literal separated fiber inverse.
The calibrated energy is verified to lie in its resolvent window throughout
this neighborhood; no complex-momentum inverse estimate is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.Auxiliary

open FreeFiber FiberAnalytic PeriodicBand Set Metric

attribute [local irreducible] scaledBand jointSeparatedResolvent fullSeparatedResolvent

def separatedRadius : ℝ := backgroundAmplitude / (2 : ℝ) ^ 30

theorem separatedRadius_pos : 0 < separatedRadius := by
  unfold separatedRadius
  exact div_pos backgroundAmplitude_pos (by positivity)

theorem band_small_difference {t : Momentum} (ht : ‖t‖ ≤ ((2 : ℝ) ^ 30)⁻¹) :
    ‖scaledBand t - scaledBand 0‖ ≤ (2 : ℝ) ^ 16 * ‖t‖ := by
  have hc : closedBall (0 : Momentum) (((2 : ℝ) ^ 13)⁻¹) ⊆ chart := by
    intro s hs j
    have hn : ‖s‖ ≤ ((2 : ℝ) ^ 13)⁻¹ := by simpa using hs
    exact ((norm_le_pi_norm s j).trans hn).trans_lt (by norm_num)
  have hb := CauchyBounds.bounded_map_sub_zero_le
    (f := scaledBand) (R := ((2 : ℝ) ^ 13)⁻¹) (C := 3) (by positivity) (by norm_num)
    (scaledBand_analytic.mono hc) (fun s hs => scaledBand_norm_le (hc hs))
    (ht.trans (by norm_num))
  apply hb.trans
  gcongr
  norm_num

theorem sampledScaledEnergy_near_zero {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64) :
    ‖sampledScaledEnergy z σ - scaledBand 0‖ ≤ 2 * backgroundAmplitude := by
  have hq0 : realMomentum (0 : Corner.Vec) = 0 := by ext j; rfl
  have hq : ‖realMomentum (0 : Corner.Vec)‖ ≤ 4 * smallRadius := by
    simpa only [hq0, norm_zero] using
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) smallRadius_pos.le)
  have hd := sampledEnergy_band_distance D hσ0 hσ (0 : Corner.Vec) hq
  have hp : fiberParameter (0 : Corner.Vec) = 0 := by
    rw [fiberParameter, hq0, unscale, smul_zero]
  rw [hp, hq0] at hd
  have h2 : h ^ 2 ≤ backgroundAmplitude ^ 2 := by
    nlinarith [D.h_pos, D.h_le, backgroundAmplitude_pos]
  have h4 : h ^ 4 ≤ h ^ 2 := by
    have hs := calibration_h_small D
    nlinarith [sq_nonneg h, mul_nonneg (sq_nonneg h) (show 0 ≤ 1 - h ^ 2 by nlinarith [D.h_pos])]
  have he : ‖sampledEnergy z σ - physicalBand 0‖ ≤ 2 * backgroundAmplitude ^ 2 := by
    rw [hd]
    have herr := abs_le.mp D.error
    change -(h ^ 4) ≤ z - ((dielectricBand 0).re - h ^ 2) ∧
      z - ((dielectricBand 0).re - h ^ 2) ≤ h ^ 4 at herr
    linarith
  have hid := totalEnergy_sub_norm (sampledScaledEnergy z σ) (scaledBand 0)
  rw [sampledScaledEnergy, totalEnergy_scaledEnergy] at hid
  change ‖sampledEnergy z σ - totalEnergy (scaledBand 0)‖ ≤ _ at he
  rw [hid] at he
  change backgroundAmplitude * ‖sampledScaledEnergy z σ - scaledBand 0‖ ≤
    2 * backgroundAmplitude ^ 2 at he
  nlinarith [backgroundAmplitude_pos]

theorem unscale_norm (q : Momentum) : ‖unscale q‖ = backgroundAmplitude⁻¹ * ‖q‖ := by
  rw [unscale, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos backgroundAmplitude_pos]

theorem separated_unscale_bound {q : Momentum} (hq : ‖q‖ ≤ separatedRadius) :
    ‖unscale q‖ ≤ ((2 : ℝ) ^ 30)⁻¹ := by
  rw [unscale_norm]
  apply (inv_mul_le_iff₀ backgroundAmplitude_pos).mpr
  simpa only [separatedRadius, div_eq_mul_inv] using hq

theorem separated_unscale_chart {q : Momentum} (hq : ‖q‖ ≤ separatedRadius) :
    unscale q ∈ chart := by
  intro j
  exact ((norm_le_pi_norm (unscale q) j).trans (separated_unscale_bound hq)).trans_lt
    (by norm_num)

theorem sampledScaledEnergy_near_complex_band {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64)
    {q : Momentum} (hq : ‖q‖ ≤ separatedRadius) :
    sampledScaledEnergy z σ ∈ closedBall (scaledBand (unscale q)) (1 / 200) := by
  rw [mem_closedBall, dist_eq_norm]
  have hq' := separated_unscale_bound hq
  have hb := band_small_difference hq'
  have he := sampledScaledEnergy_near_zero D hσ0 hσ
  have htri := norm_add_le (sampledScaledEnergy z σ - scaledBand 0)
    (scaledBand 0 - scaledBand (unscale q))
  rw [sub_add_sub_cancel, norm_sub_rev (scaledBand 0)] at htri
  have hc : 2 * backgroundAmplitude + (2 : ℝ)^16 * ((2 : ℝ)^30)⁻¹ ≤ 1 / 200 := by
    norm_num [backgroundAmplitude]
  nlinarith

def separatedSymbol (z σ : ℝ) (q : Momentum) : FiberMap :=
  jointSeparatedResolvent (unscale q, sampledScaledEnergy z σ)

theorem separatedSymbol_eq {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64)
    {q : Momentum} (hq : ‖q‖ ≤ separatedRadius) :
    separatedSymbol z σ q = fullSeparatedResolvent (unscale q) (sampledScaledEnergy z σ) :=
  jointSeparatedResolvent_eq (separated_unscale_chart hq)
    (centeredEnergyDisk_subset (separated_unscale_chart hq)
      (sampledScaledEnergy_near_complex_band D hσ0 hσ hq))

theorem separatedSymbol_norm_le {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64)
    {q : Momentum} (hq : ‖q‖ ≤ separatedRadius) :
    ‖separatedSymbol z σ q‖ ≤ (2 : ℝ)^112 :=
  jointSeparatedResolvent_norm_le (separated_unscale_chart hq)
    (sampledScaledEnergy_near_complex_band D hσ0 hσ hq)

theorem separatedSymbol_analytic {h z σ : ℝ} (D : Calibration h z)
    (hσ0 : 0 ≤ σ) (hσ : σ ≤ h ^ 4 / 64) :
    AnalyticOnNhd ℂ (separatedSymbol z σ) (closedBall 0 separatedRadius) := by
  intro q hq
  have hq' : ‖q‖ ≤ separatedRadius := by simpa using hq
  have hu : AnalyticAt ℂ unscale q := by
    exact ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := Momentum) (F := Momentum)
      ((backgroundAmplitude : ℂ)⁻¹ • ContinuousLinearMap.id ℂ Momentum) q
  have he := sampledScaledEnergy_near_complex_band D hσ0 hσ hq'
  exact AnalyticAt.comp (f := fun q : Momentum => (unscale q, sampledScaledEnergy z σ))
    (jointSeparatedResolvent_analyticAt (separated_unscale_chart hq')
      (centeredEnergyDisk_subset (separated_unscale_chart hq') he))
    (hu.prod analyticAt_const)

#print axioms sampledScaledEnergy_near_complex_band
#print axioms separatedSymbol_analytic
#print axioms separatedSymbol_norm_le

end Maxwell.Continuum.Auxiliary
