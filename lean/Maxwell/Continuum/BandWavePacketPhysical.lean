import Maxwell.Continuum.BandWavePacketSection
import Maxwell.Continuum.BandWavePacketProjection

/-! The band packets and their orthogonal projection live in the actual
physical L² field space through the constructed continuum Bloch unitary. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.BandWavePacket

open MeasureTheory FreeFiber Bloch

def physicalEmbedding : Amplitude →ₗᵢ[ℂ] FieldL2 :=
  unitary.symm.toLinearIsometry.comp fiberEmbedding

theorem physicalEmbedding_norm (f : Amplitude) : ‖physicalEmbedding f‖ = ‖f‖ :=
  physicalEmbedding.norm_map f

theorem physicalEmbedding_inner (f g : Amplitude) :
    inner ℂ (physicalEmbedding f) (physicalEmbedding g) = inner ℂ f g :=
  physicalEmbedding.inner_map_map f g

theorem unitary_physicalEmbedding (f : Amplitude) :
    unitary (physicalEmbedding f) = fiberEmbedding f := unitary.apply_symm_apply _

def physicalAnalysis : FieldL2 →L[ℂ] Amplitude :=
  actualSection.analysis.comp unitary.toContinuousLinearEquiv.toContinuousLinearMap

def physicalProjection : FieldL2 →L[ℂ] FieldL2 :=
  physicalEmbedding.toContinuousLinearMap.comp physicalAnalysis

theorem physicalAnalysis_embedding (f : Amplitude) :
    physicalAnalysis (physicalEmbedding f) = f := by
  change actualSection.analysis (unitary (physicalEmbedding f)) = f
  rw [unitary_physicalEmbedding]
  exact actualSection.analysis_embedding f

theorem unitary_physicalProjection (f : FieldL2) :
    unitary (physicalProjection f) = actualSection.projection (unitary f) := by
  change unitary (physicalEmbedding (physicalAnalysis f)) = _
  rw [unitary_physicalEmbedding]
  rfl

theorem physicalProjection_idempotent : physicalProjection * physicalProjection = physicalProjection := by
  apply ContinuousLinearMap.ext
  intro f
  change physicalEmbedding (physicalAnalysis (physicalEmbedding (physicalAnalysis f))) = _
  rw [physicalAnalysis_embedding]
  rfl

theorem physicalProjection_symmetric : physicalProjection.IsSymmetric := by
  intro f g
  change inner ℂ (physicalProjection f) g = inner ℂ f (physicalProjection g)
  rw [← unitary.inner_map_map, ← unitary.inner_map_map f (physicalProjection g),
    unitary_physicalProjection, unitary_physicalProjection]
  exact actualSection.projection_symmetric _ _

theorem physicalProjection_norm_le (f : FieldL2) : ‖physicalProjection f‖ ≤ ‖f‖ := by
  rw [← unitary.norm_map (physicalProjection f), unitary_physicalProjection, ← unitary.norm_map f]
  exact actualSection.projection_norm_le _

theorem physicalProjection_range :
    LinearMap.range physicalProjection.toLinearMap = LinearMap.range physicalEmbedding.toLinearMap := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨physicalAnalysis g, rfl⟩
  · rintro ⟨g, rfl⟩
    refine ⟨physicalEmbedding g, ?_⟩
    change physicalEmbedding (physicalAnalysis (physicalEmbedding g)) = physicalEmbedding g
    rw [physicalAnalysis_embedding]

theorem physical_range_iff (f : FieldL2) :
    f ∈ LinearMap.range physicalEmbedding.toLinearMap ↔
      ∀ᵐ q ∂quasiMeasure, unitary f q ∈ ℂ ∙ sectionValue q := by
  change f ∈ LinearMap.range physicalEmbedding.toLinearMap ↔
    ∀ᵐ q ∂quasiMeasure, unitary f q ∈ ℂ ∙ actualSection.value q
  rw [← actualSection.range_iff (unitary f)]
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨g, ?_⟩
    exact (unitary_physicalEmbedding g).symm
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    apply unitary.injective
    change unitary (physicalEmbedding g) = unitary f
    rw [unitary_physicalEmbedding]
    exact hg

theorem physicalProjection_fiber_ae (f : FieldL2) :
    unitary (physicalProjection f) =ᵐ[quasiMeasure]
      fun q => (inner ℂ (sectionValue q) (unitary f q)) • sectionValue q := by
  rw [unitary_physicalProjection]
  exact actualSection.projection_ae _

#print axioms physicalEmbedding_norm
#print axioms physicalProjection_idempotent
#print axioms physicalProjection_symmetric
#print axioms physical_range_iff

end Maxwell.Continuum.BandWavePacket
