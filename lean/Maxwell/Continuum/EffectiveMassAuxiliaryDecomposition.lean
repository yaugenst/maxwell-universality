import Maxwell.Continuum.EffectiveMassSelectedFiber
import Maxwell.Continuum.EffectiveMassAuxiliaryTranslation

/-! Exact selected/separated decomposition of the actual scaled Sh.
The selected term is the literal Bh Bh†, and the error is the full
separated continuum resolvent, with the explicit 2^112 h² bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory Auxiliary Bloch BandWavePacket FreeFiber PeriodicBand
open scoped InnerProduct

attribute [local irreducible] Bloch.unitary Auxiliary.resolvent

def packetError {h z : ℝ} (D : Calibration h z) : FieldL2 →L[ℂ] FieldL2 :=
  (h^2 : ℂ) • resolvent D le_rfl (by positivity) - (packetBand D).comp ((packetBand D)†)

set_option maxHeartbeats 800000 in
theorem packetError_ae {h z : ℝ} (D : Calibration h z) (f : FieldL2) :
    unitary (packetError D f) =ᵐ[quasiMeasure] fun q =>
      (h^2 : ℂ) • cutoffFiber z 0 q (unitary f q) -
        (inner ℂ ((weightedSection D).coefficient q) (unitary f q)) • (weightedSection D).coefficient q := by
  change unitary ((h^2 : ℂ) • resolvent D le_rfl (by positivity) f -
    packetBand D (((packetBand D)†) f)) =ᵐ[quasiMeasure] _
  rw [map_sub, map_smul]
  filter_upwards [resolvent_ae D le_rfl (by positivity : (0:ℝ) ≤ h^4/64) f,
    packetBand_gram_ae D f,
    Lp.coeFn_smul (h^2 : ℂ) (unitary (resolvent D le_rfl (by positivity) f)),
    Lp.coeFn_sub ((h^2 : ℂ) • unitary (resolvent D le_rfl (by positivity) f))
      (unitary (packetBand D (((packetBand D)†) f)))] with q hr hp hs hd
  rw [hd, Pi.sub_apply, hs, Pi.smul_apply, hr, hp]

theorem packetError_separated_ae {h z : ℝ} (D : Calibration h z) (f : FieldL2) :
    unitary (packetError D f) =ᵐ[quasiMeasure]
      cutoffRegion.indicator (fun q => ((h^2 * cutoff q.val : ℝ) : ℂ) •
        fullSeparatedResolvent (parameter q) (sampledScaledEnergy z 0) (unitary f q)) := by
  filter_upwards [packetError_ae D f] with q hq
  rw [hq]
  by_cases hc : q ∈ cutoffRegion
  · rw [Set.indicator_of_mem hc]
    exact selectedFiber_error_eq D hc (unitary f q)
  · have hz : (weightedSection D).coefficient q = 0 := by
      change (cutoffBandMultiplier h z (h⁻¹ • q.val) : ℂ) • sectionValue q = 0
      rw [cutoff_scaled_band_zero D hc, Complex.ofReal_zero, zero_smul]
    rw [Set.indicator_of_notMem hc, cutoffFiber_zero hc, zero_apply,
      smul_zero, hz, smul_zero, sub_self]

theorem packetError_norm_le {h z : ℝ} (D : Calibration h z) :
    ‖packetError D‖ ≤ (2 : ℝ)^112 * h^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  rw [← unitary.norm_map (packetError D f), ← unitary.norm_map f]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [packetError_ae D f] with q hq
  rw [hq]
  exact selectedFiber_error_bound D q (unitary f q)

theorem Bh_gram {h z : ℝ} (D : Calibration h z) :
    (Bh D).comp ((Bh D)†) =
      (Qh h).comp (((packetBand D).comp ((packetBand D)†)).comp (Qh h)) := by
  have hB : Bh D = (Qh h).comp (packetBand D) := rfl
  rw [hB, ContinuousLinearMap.adjoint_comp, (Qh_selfAdjoint h).adjoint_eq]
  apply ContinuousLinearMap.ext
  intro f
  rfl

theorem Sh_band_difference_eq {h z : ℝ} (D : Calibration h z) :
    (h^2 : ℂ) • Sh D - (Bh D).comp ((Bh D)†) = Qh h * packetError D * Qh h := by
  rw [Bh_gram]
  apply ContinuousLinearMap.ext
  intro f
  change (h^2 : ℂ) • Qh h (resolvent D le_rfl (by positivity) (Qh h f)) -
      Qh h (packetBand D (((packetBand D)†) (Qh h f))) =
    Qh h ((h^2 : ℂ) • resolvent D le_rfl (by positivity) (Qh h f) -
      packetBand D (((packetBand D)†) (Qh h f)))
  rw [map_sub, map_smul]

theorem Sh_selected_separated {h z : ℝ} (D : Calibration h z) :
    (h^2 : ℂ) • Sh D = (Bh D).comp ((Bh D)†) + Qh h * packetError D * Qh h := by
  have he := Sh_band_difference_eq D
  exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)

theorem Sh_band_difference_norm_le {h z : ℝ} (D : Calibration h z) :
    ‖(h^2 : ℂ) • Sh D - (Bh D).comp ((Bh D)†)‖ ≤ (2 : ℝ)^112 * h^2 := by
  rw [Sh_band_difference_eq]
  calc
    _ ≤ (‖Qh h‖ * ‖packetError D‖) * ‖Qh h‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * ((2 : ℝ)^112 * h^2)) * 1 := by
      gcongr
      · exact Qh_norm_le h
      · exact packetError_norm_le D
      · exact Qh_norm_le h
    _ = _ := by ring

#print axioms Sh_band_difference_norm_le
#print axioms packetError_separated_ae

end Maxwell.Continuum.EffectiveMass
