import Maxwell.Continuum.BandWavePacketLp
import Maxwell.Continuum.FiberNormalizationNormalized
import Maxwell.Continuum.PeriodicPhysicalBand
import Maxwell.Continuum.BlochPeriodicGraph

/-! The actual normalized periodic-band section on the physical Bloch
cell. It is extended by zero outside the constructed local momentum chart. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 2048

namespace Maxwell.Continuum.BandWavePacket

open MeasureTheory FreeFiber FiberNormalization PeriodicBand Bloch

attribute [local irreducible] PeriodicPerturbation.perturbation PeriodicPerturbation.finiteK
  CornerBridge.topState RankOneBand.Data.bandRoot scaledBand clusterVector
  fiberVector normalizedFiberVector

def parameter (q : QuasiCell) : Momentum := unscale (quasiMomentum q)

def region : Set QuasiCell := parameter ⁻¹' chart

theorem parameter_real (q : QuasiCell) :
    parameter q = realMomentum (fun j => (q.val j) / backgroundAmplitude) := by
  funext j
  simp only [parameter, unscale, quasiMomentum, realMomentum, Pi.smul_apply, smul_eq_mul,
    div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv]
  ring

theorem parameter_continuous : Continuous parameter := by
  unfold parameter unscale quasiMomentum
  apply continuous_pi
  intro j
  exact continuous_const.mul
    (Complex.continuous_ofReal.comp ((PiLp.continuous_apply 2 _ j).comp continuous_subtype_val))

theorem region_isOpen : IsOpen region := chart_isOpen.preimage parameter_continuous

theorem section_continuousOn :
    ContinuousOn (fun q => normalizedFiberVector (parameter q)) region :=
  normalizedFiberVector_analytic.continuousOn.comp parameter_continuous.continuousOn
    (fun _ hq => hq)

def sectionValue : QuasiCell → FiberSpace :=
  region.indicator (fun q => normalizedFiberVector (parameter q))

theorem sectionValue_measurable : AEStronglyMeasurable sectionValue quasiMeasure :=
  (aestronglyMeasurable_indicator_iff region_isOpen.measurableSet).mpr
    (section_continuousOn.aestronglyMeasurable region_isOpen.measurableSet)

theorem sectionValue_eq {q : QuasiCell} (hq : q ∈ region) :
    sectionValue q = normalizedFiberVector (parameter q) := Set.indicator_of_mem hq _

theorem sectionValue_zero {q : QuasiCell} (hq : q ∉ region) : sectionValue q = 0 :=
  Set.indicator_of_notMem hq _

theorem sectionValue_unit {q : QuasiCell} (hq : q ∈ region) : ‖sectionValue q‖ = 1 := by
  rw [sectionValue_eq hq, parameter_real]
  apply normalizedFiberVector_norm_real
  rwa [← parameter_real]

def actualSection : SectionData (H := FiberSpace) quasiMeasure region where
  value := sectionValue
  measurable := sectionValue_measurable
  unit := fun _ hq => sectionValue_unit hq
  zero := fun _ hq => sectionValue_zero hq

abbrev Amplitude := amplitudes quasiMeasure region

def fiberEmbedding : Amplitude →ₗᵢ[ℂ] FiberL2 := actualSection.embedding

theorem fiberEmbedding_ae (f : Amplitude) :
    fiberEmbedding f =ᵐ[quasiMeasure] fun q => f.val q • sectionValue q :=
  actualSection.embedding_ae f

theorem fiberEmbedding_norm (f : Amplitude) : ‖fiberEmbedding f‖ = ‖f‖ :=
  fiberEmbedding.norm_map f

theorem sectionValue_graph {q : QuasiCell} (hq : q ∈ region) :
    (sectionValue q, 0) ∈ (materialFiber (quasiMomentum q)
      (dielectricBand (quasiMomentum q) + 7) backgroundAmplitude).graph := by
  have h := normalizedFiberVector_graph hq
  rw [sectionValue_eq hq]
  change (normalizedFiberVector (parameter q), 0) ∈ _
  have hq' : scaledMomentum (parameter q) = quasiMomentum q := scaledMomentum_unscale _
  have hE : dielectricBand (quasiMomentum q) + 7 = totalEnergy (scaledBand (parameter q)) := by
    unfold dielectricBand physicalBand parameter
    ring
  rwa [hq', ← hE] at h

#print axioms actualSection
#print axioms fiberEmbedding_norm
#print axioms sectionValue_graph

end Maxwell.Continuum.BandWavePacket
