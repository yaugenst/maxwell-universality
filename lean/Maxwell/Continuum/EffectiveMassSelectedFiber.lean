import Maxwell.Continuum.EffectiveMassSelectedPacket
import Maxwell.Continuum.BandWavePacketSpectral

/-! The selected packet Gram is exactly the pole term of the actual
cutoff fiber inverse. The remaining fiber is the already proved analytic
separated resolvent, with all aliases and longitudinal fields retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory Auxiliary Bloch BandWavePacket FreeFiber PeriodicBand FiberAnalytic
open scoped InnerProduct

attribute [local irreducible] fullResolventExtension scaledBand fullSeparatedResolvent
  PeriodicPerturbation.perturbation PeriodicPerturbation.finiteK CornerBridge.topState
  RankOneBand.Data.bandRoot

theorem cutoffRegion_bandRegion {q : QuasiCell} (hq : q ∈ cutoffRegion) : q ∈ region :=
  fiberParameter_chart q.val.ofLp (show ‖quasiMomentum q‖ ≤ 4 * smallRadius from hq.le)

theorem bandValue_cast {q : QuasiCell} (hq : q ∈ cutoffRegion) :
    (bandValue q.val : ℂ) = dielectricBand (quasiMomentum q) :=
  dielectricBand_ofReal_re q.val.ofLp
    (small_momentum_mem_physicalChart (show ‖quasiMomentum q‖ ≤ 4 * smallRadius from hq.le))

theorem cutoff_scaled_band_square {h z : ℝ} (D : Calibration h z) {q : QuasiCell}
    (hq : q ∈ cutoffRegion) :
    cutoffBandMultiplier h z (h⁻¹ • q.val)^2 = h^2 * cutoff q.val / (bandValue q.val-z) := by
  have hd := (calibration_denominator_bounds D le_rfl (by positivity : (0:ℝ) ≤ h^4/64)
    q.val.ofLp (show ‖quasiMomentum q‖ ≤ 4 * smallRadius from hq.le)).1
  change h^2/2 ≤ bandValue q.val - (z+0) at hd
  have hp : 0 ≤ bandValue q.val-z := by nlinarith [sq_nonneg h]
  rw [cutoffBandMultiplier_physical D, smul_smul, mul_inv_cancel₀ D.h_pos.ne', one_smul,
    div_pow, mul_pow, Real.sq_sqrt (cutoff_nonneg q.val), Real.sq_sqrt hp]

theorem cutoff_scaled_band_zero {h z : ℝ} (D : Calibration h z) {q : QuasiCell}
    (hq : q ∉ cutoffRegion) : cutoffBandMultiplier h z (h⁻¹ • q.val) = 0 := by
  rw [cutoffBandMultiplier, smul_smul, mul_inv_cancel₀ D.h_pos.ne', one_smul,
    cutoff_eq_zero_outside hq, Real.sqrt_zero, zero_mul]

theorem fiberResolvent_selected {h z : ℝ} (D : Calibration h z) {q : QuasiCell}
    (hq : q ∈ cutoffRegion) :
    fiberResolvent z 0 q.val.ofLp = ((bandValue q.val-z : ℝ) : ℂ)⁻¹ •
      fullSpectralProjection (parameter q) +
      fullSeparatedResolvent (parameter q) (sampledScaledEnergy z 0) := by
  have hq' : ‖quasiMomentum q‖ ≤ 4 * smallRadius := hq.le
  have he := sampledScaledEnergy_mem D le_rfl (by positivity : (0:ℝ) ≤ h^4/64) q.val.ofLp hq'
  have hne := sampledScaledEnergy_ne_band D le_rfl (by positivity : (0:ℝ) ≤ h^4/64) q.val.ofLp hq'
  have ht := cutoffRegion_bandRegion hq
  have hp := fullResolvent_pole_formula ht (centeredEnergyDisk_subset ht he) hne
  change fiberResolvent z 0 q.val.ofLp = _ at hp
  have hd : (backgroundAmplitude : ℂ) * (sampledScaledEnergy z 0 - scaledBand (parameter q)) =
      -((bandValue q.val-z : ℝ) : ℂ) := by
    rw [← totalEnergy_sub, sampledScaledEnergy, totalEnergy_scaledEnergy]
    have hb : physicalBand (parameter q) = dielectricBand (quasiMomentum q) + 7 := by
      unfold dielectricBand parameter
      ring
    change sampledEnergy z 0 - physicalBand (parameter q) = _
    rw [hb, ← bandValue_cast hq]
    unfold sampledEnergy
    push_cast
    ring
  rw [hd] at hp
  rw [hp]
  congr 1
  rw [inv_neg, fullSpectralProjection]
  module

theorem weightedSection_gram_eq {h z : ℝ} (D : Calibration h z) {q : QuasiCell}
    (hq : q ∈ cutoffRegion) (v : FiberSpace) :
    (inner ℂ ((weightedSection D).coefficient q) v) • (weightedSection D).coefficient q =
      ((h^2 * cutoff q.val / (bandValue q.val-z) : ℝ) : ℂ) •
        fullSpectralProjection (parameter q) v := by
  change (inner ℂ ((cutoffBandMultiplier h z (h⁻¹ • q.val) : ℂ) • sectionValue q) v) •
      ((cutoffBandMultiplier h z (h⁻¹ • q.val) : ℂ) • sectionValue q) = _
  rw [inner_smul_left, Complex.conj_ofReal, spectralProjection_section (cutoffRegion_bandRegion hq)]
  have hc := congrArg (fun x : ℝ => (x : ℂ)) (cutoff_scaled_band_square D hq)
  simp only [Complex.ofReal_pow] at hc
  rw [smul_smul, smul_smul, ← hc]
  congr 1
  ring

theorem selectedFiber_error_eq {h z : ℝ} (D : Calibration h z) {q : QuasiCell}
    (hq : q ∈ cutoffRegion) (v : FiberSpace) :
    (h^2 : ℂ) • cutoffFiber z 0 q v -
      (inner ℂ ((weightedSection D).coefficient q) v) • (weightedSection D).coefficient q =
      ((h^2 * cutoff q.val : ℝ) : ℂ) •
        fullSeparatedResolvent (parameter q) (sampledScaledEnergy z 0) v := by
  rw [cutoffFiber_eq hq, fiberResolvent_selected D hq, weightedSection_gram_eq D hq]
  simp only [smul_apply, add_apply, smul_add, smul_smul]
  have hc : (h^2 : ℂ) * (cutoff q.val : ℂ) * ((bandValue q.val-z : ℝ) : ℂ)⁻¹ =
      ((h^2 * cutoff q.val / (bandValue q.val-z) : ℝ) : ℂ) := by push_cast; ring
  rw [← mul_assoc, hc]
  push_cast
  abel

theorem selectedFiber_error_bound {h z : ℝ} (D : Calibration h z)
    (q : QuasiCell) (v : FiberSpace) :
    ‖(h^2 : ℂ) • cutoffFiber z 0 q v -
      (inner ℂ ((weightedSection D).coefficient q) v) • (weightedSection D).coefficient q‖ ≤
        ((2 : ℝ)^112 * h^2) * ‖v‖ := by
  by_cases hq : q ∈ cutoffRegion
  · rw [selectedFiber_error_eq D hq, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (sq_nonneg h) (cutoff_nonneg q.val))]
    have hs := fullSeparatedResolvent_norm_le (cutoffRegion_bandRegion hq)
      (sampledScaledEnergy_mem D le_rfl (by positivity : (0:ℝ) ≤ h^4/64)
        q.val.ofLp (show ‖quasiMomentum q‖ ≤ 4 * smallRadius from hq.le))
    have hn := (fullSeparatedResolvent (parameter q) (sampledScaledEnergy z 0)).le_of_opNorm_le hs v
    calc
      _ ≤ (h^2 * 1) * ((2 : ℝ)^112 * ‖v‖) := by
        gcongr
        exact cutoff_le_one q.val
      _ = _ := by ring
  · have hz : (weightedSection D).coefficient q = 0 := by
      change (cutoffBandMultiplier h z (h⁻¹ • q.val) : ℂ) • sectionValue q = 0
      rw [cutoff_scaled_band_zero D hq, Complex.ofReal_zero, zero_smul]
    rw [cutoffFiber_zero hq, zero_apply, smul_zero, hz, smul_zero, sub_self, norm_zero]
    positivity

end Maxwell.Continuum.EffectiveMass
