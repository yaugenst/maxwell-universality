import Maxwell.Continuum.EffectiveMassConstantPacket

/-! The actual variable-mode and fixed-mode physical packets are close
in operator norm, by the complete Fourier-vector multiplier estimate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory FreeFiber Bloch BandWavePacket PeriodicBand Auxiliary

attribute [local irreducible] FiberNormalization.normalizedFiberVector physicalFiberVector

theorem sectionValue_scaled {h : ℝ} (hh : 0 < h) (q : QuasiCell) (hq : q ∈ region) :
    sectionValue q = scaledFiber h (h⁻¹ • q.val) := by
  rw [sectionValue_eq hq, scaledFiber, smul_smul, mul_inv_cancel₀ hh.ne', one_smul]
  rw [physicalFiberVector]
  rfl

theorem scaledAmplitude_scalarProduct {h : ℝ} (hh : 0 < h)
    (M : ScalarL2 →L[ℂ] ScalarL2) (a : Space → ℂ) (f : ScalarL2)
    (hM : M f =ᵐ[volume] fun p => a p * f p) :
    (scaledAmplitude hh (M f)).val =ᵐ[quasiMeasure]
      region.indicator (fun q =>
        (amplitudeFactor h : ℂ) * (a (h⁻¹ • q.val) * f (h⁻¹ • q.val))) := by
  filter_upwards [scaledAmplitude_ae hh (M f), quasi_coe_ae (inverseDilation_ae hh hM)]
    with q hs hm
  rw [hs]
  by_cases hq : q ∈ region
  · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq, hm]
  · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq]

theorem packetFiber_difference_norm {h z : ℝ} (D : Calibration h z) (f : ScalarL2) :
    ‖fiberEmbedding (scaledAmplitude D.h_pos (cutoffAmplitudeOperator D f)) -
      constantSection.embedding (scaledAmplitude D.h_pos (referenceScalarOperator f))‖ ≤
        ((2 : ℝ)^130 * h) * ‖f‖ := by
  let g := angularToQuasi (scaledAngular D.h_pos f)
  have hg : g =ᵐ[quasiMeasure] fun q =>
      (amplitudeFactor h : ℂ) * f (h⁻¹ • q.val) := by
    filter_upwards [angularToQuasi_ae (scaledAngular D.h_pos f),
      quasi_coe_ae (scaledAngular_ae D.h_pos f)] with q hq hs
    exact hq.trans hs
  have hnorm : ‖g‖ ≤ ‖f‖ :=
    (angularToQuasi_norm_le _).trans_eq (scaledAngular_norm D.h_pos f)
  have hb : ‖fiberEmbedding (scaledAmplitude D.h_pos (cutoffAmplitudeOperator D f)) -
      constantSection.embedding (scaledAmplitude D.h_pos (referenceScalarOperator f))‖ ≤
      ((2 : ℝ)^130 * h) * ‖g‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [fiberEmbedding_ae (scaledAmplitude D.h_pos (cutoffAmplitudeOperator D f)),
      constantFiber_ae (scaledAmplitude D.h_pos (referenceScalarOperator f)),
      Lp.coeFn_sub (fiberEmbedding (scaledAmplitude D.h_pos (cutoffAmplitudeOperator D f)))
        (constantSection.embedding (scaledAmplitude D.h_pos (referenceScalarOperator f))),
      scaledAmplitude_scalarProduct D.h_pos (cutoffAmplitudeOperator D)
        (fun p => (cutoffBandMultiplier h z p : ℂ)) f (cutoffAmplitudeOperator_ae D f),
      scaledAmplitude_scalarProduct D.h_pos referenceScalarOperator
        (fun p => (referenceMultiplier p : ℂ)) f (referenceScalarOperator_ae f), hg]
      with q hv hc hsub hs hr hgq
    rw [hsub, Pi.sub_apply, hv, hc, hs, hr]
    by_cases hq : q ∈ region
    · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq,
        sectionValue_scaled D.h_pos q hq, hgq]
      have hid :
          ((amplitudeFactor h : ℂ) * ((cutoffBandMultiplier h z (h⁻¹ • q.val) : ℂ) *
              f (h⁻¹ • q.val))) • scaledFiber h (h⁻¹ • q.val) -
          ((amplitudeFactor h : ℂ) * ((referenceMultiplier (h⁻¹ • q.val) : ℂ) *
              f (h⁻¹ • q.val))) • physicalFiberVector 0 =
          ((amplitudeFactor h : ℂ) * f (h⁻¹ • q.val)) •
            (vectorMultiplier h z (h⁻¹ • q.val) - referenceVectorMultiplier (h⁻¹ • q.val)) := by
        simp only [vectorMultiplier, referenceVectorMultiplier, smul_sub, smul_smul]
        module
      rw [hid, norm_smul]
      simpa only [mul_comm ((2 : ℝ)^130 * h)] using
        mul_le_mul_of_nonneg_left (vectorMultiplier_error D (h⁻¹ • q.val))
          (norm_nonneg ((amplitudeFactor h : ℂ) * f (h⁻¹ • q.val)))
    · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq, zero_smul,
        zero_smul, sub_self, norm_zero]
      exact mul_nonneg (mul_nonneg (by positivity) D.h_pos.le) (norm_nonneg _)
  exact hb.trans (mul_le_mul_of_nonneg_left hnorm (mul_nonneg (by positivity) D.h_pos.le))

theorem rawPacket_difference_norm {h z : ℝ} (D : Calibration h z) (f : ScalarL2) :
    ‖Uh D.h_pos (cutoffAmplitudeOperator D f) - constantUh D.h_pos (referenceScalarOperator f)‖ ≤
      ((2 : ℝ)^130 * h) * ‖f‖ := by
  rw [← unitary.norm_map, map_sub, Uh_unitary, constantUh_unitary, ← smul_sub,
    norm_smul, Complex.norm_I, one_mul]
  exact packetFiber_difference_norm D f

theorem Bh_constantPacket_error {h z : ℝ} (D : Calibration h z) :
    ‖Bh D - constantPacketReconstruction D.h_pos‖ ≤ (2 : ℝ)^130 * h := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by positivity) D.h_pos.le)
  intro f
  change ‖Qh h (Uh D.h_pos (cutoffAmplitudeOperator D f)) -
    Qh h (constantUh D.h_pos (referenceScalarOperator f))‖ ≤ _
  rw [← map_sub]
  have hQ := (Qh h).le_of_opNorm_le (Qh_norm_le h)
    (Uh D.h_pos (cutoffAmplitudeOperator D f) - constantUh D.h_pos (referenceScalarOperator f))
  rw [one_mul] at hQ
  exact hQ.trans (rawPacket_difference_norm D f)

end Maxwell.Continuum.EffectiveMass
