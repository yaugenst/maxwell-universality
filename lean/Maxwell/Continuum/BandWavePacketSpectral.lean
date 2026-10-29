import Maxwell.Continuum.BandWavePacketPhysical
import Maxwell.Continuum.BandWavePacketReality
import Maxwell.Continuum.PeriodicBandProjectionAnalytic

/-! The physical packet projection is exactly the chart restriction of
the full infinite-fiber spectral projection obtained from its resolvent pole. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.BandWavePacket

open FreeFiber FiberNormalization PeriodicBand Bloch

attribute [local irreducible] PeriodicPerturbation.perturbation PeriodicPerturbation.finiteK
  CornerBridge.topState RankOneBand.Data.bandRoot scaledBand clusterVector
  fiberVector normalizedFiberVector

theorem spectralProjection_section {q : QuasiCell} (hq : q ∈ region) (v : FiberSpace) :
    fullSpectralProjection (parameter q) v = (inner ℂ (sectionValue q) v) • sectionValue q := by
  rw [fullSpectralProjection_eq_bilinearProjection hq]
  change (bilinear (normalizedFiberVector (parameter q)) v) • normalizedFiberVector (parameter q) = _
  rw [← sectionValue_eq hq, sectionValue_bilinear_inner]

theorem physicalProjection_spectral_ae (f : FieldL2) :
    unitary (physicalProjection f) =ᵐ[quasiMeasure]
      region.indicator (fun q => fullSpectralProjection (parameter q) (unitary f q)) := by
  filter_upwards [physicalProjection_fiber_ae f] with q hq
  rw [hq]
  by_cases hs : q ∈ region
  · rw [Set.indicator_of_mem hs, spectralProjection_section hs]
  · rw [Set.indicator_of_notMem hs, sectionValue_zero hs, smul_zero]

#print axioms physicalProjection_spectral_ae

end Maxwell.Continuum.BandWavePacket
