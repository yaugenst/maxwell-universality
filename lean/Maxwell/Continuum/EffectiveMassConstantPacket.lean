import Maxwell.Continuum.EffectiveMassBandOperator
import Maxwell.Continuum.EffectiveMassReferenceSpectrum

/-! The constant zero-momentum Bloch packet, with the same actual
quasimomentum chart and scaling as the variable-band packet. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory FreeFiber Bloch BandWavePacket PeriodicBand

def constantSection : SectionData (H := FiberSpace) quasiMeasure region where
  value := region.indicator (fun _ => physicalFiberVector 0)
  measurable := aestronglyMeasurable_const.indicator region_isOpen.measurableSet
  unit := fun q hq => by
    rw [Set.indicator_of_mem hq]
    exact physicalFiberVector_zero_norm
  zero := fun q hq => Set.indicator_of_notMem hq _

def constantPhysicalEmbedding : Amplitude →ₗᵢ[ℂ] FieldL2 :=
  unitary.symm.toLinearIsometry.comp constantSection.embedding

theorem constantPhysicalEmbedding_unitary (f : Amplitude) :
    unitary (constantPhysicalEmbedding f) = constantSection.embedding f :=
  unitary.apply_symm_apply _

theorem constantFiber_ae (f : Amplitude) :
    constantSection.embedding f =ᵐ[quasiMeasure]
      fun q => f.val q • physicalFiberVector 0 := by
  filter_upwards [constantSection.embedding_ae f, f.property] with q he hf
  rw [he]
  by_cases hq : q ∈ region
  · change f.val q • region.indicator (fun _ => physicalFiberVector 0) q = _
    rw [Set.indicator_of_mem hq]
  · rw [hf hq, zero_smul, zero_smul]

def constantUh {h : ℝ} (hh : 0 < h) : ScalarL2 →L[ℂ] FieldL2 :=
  Complex.I • (constantPhysicalEmbedding.toContinuousLinearMap.comp (scaledAmplitude hh))

theorem constantUh_unitary {h : ℝ} (hh : 0 < h) (f : ScalarL2) :
    unitary (constantUh hh f) = Complex.I • constantSection.embedding (scaledAmplitude hh f) := by
  change unitary (Complex.I • constantPhysicalEmbedding (scaledAmplitude hh f)) = _
  rw [map_smul, constantPhysicalEmbedding_unitary]

theorem constantUh_norm_le {h : ℝ} (hh : 0 < h) (f : ScalarL2) : ‖constantUh hh f‖ ≤ ‖f‖ := by
  change ‖Complex.I • constantPhysicalEmbedding (scaledAmplitude hh f)‖ ≤ _
  rw [norm_smul, Complex.norm_I, one_mul, constantPhysicalEmbedding.norm_map]
  exact scaledAmplitude_norm_le hh f

def constantPacketReconstruction {h : ℝ} (hh : 0 < h) : ScalarL2 →L[ℂ] FieldL2 :=
  (Qh h).comp ((constantUh hh).comp referenceScalarOperator)

theorem constantPacketReconstruction_norm {h : ℝ} (hh : 0 < h) :
    ‖constantPacketReconstruction hh‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖Qh h (constantUh hh (referenceScalarOperator f))‖ ≤ 1 * ‖f‖
  rw [one_mul]
  calc
    _ ≤ ‖constantUh hh (referenceScalarOperator f)‖ := by
      simpa only [one_mul] using (Qh h).le_of_opNorm_le (Qh_norm_le h)
        (constantUh hh (referenceScalarOperator f))
    _ ≤ ‖referenceScalarOperator f‖ := constantUh_norm_le hh _
    _ ≤ ‖f‖ := referenceProfile.multiplier_apply_norm_le f

end Maxwell.Continuum.EffectiveMass
