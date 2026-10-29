import Maxwell.Continuum.EffectiveMassPacketWave
import Maxwell.Continuum.EffectiveMassGramHilbert
import Maxwell.Continuum.EffectiveMassKernelGram

/-! The exact well-weighted Gram form of the genuine physical Bloch
embedding. The right side is derived by dominated Fubini from its actual
inverse Fourier reconstruction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory FreeFiber Bloch BandWavePacket CellBandFourier

def waveGram (h : ℝ) (q r : QuasiCell) : ℂ :=
  ∫ x, (Well.w (h • x) : ℂ) * inner ℂ (packetWave q x) (packetWave r x)

theorem physicalEmbedding_well_gram {h : ℝ} (hh : 0 < h) (f g : Amplitude) :
    inner ℂ (physicalEmbedding f) (Wh h (physicalEmbedding g)) =
      ∫ q, star (f.val q) * (∫ r, g.val r * waveGram h q r ∂quasiMeasure) ∂quasiMeasure := by
  rw [field_inner_eq_integral]
  have he : (fun x => inner ℂ (fieldValue (physicalEmbedding f) x)
      (fieldValue (Wh h (physicalEmbedding g)) x)) =ᵐ[volume]
      fun x => (Well.w (h • x) : ℂ) * inner ℂ
        (∫ q, f.val q • packetWave q x ∂quasiMeasure)
        (∫ r, g.val r • packetWave r x ∂quasiMeasure) := by
    filter_upwards [physicalEmbedding_vector_integral f, physicalEmbedding_vector_integral g,
      fieldValue_Wh_ae h (physicalEmbedding g)] with x hf hg hw
    rw [hw, hf, hg, inner_smul_right]
  rw [integral_congr_ae he]
  exact bounded_hilbert_wave_gram (fun xq : Space × QuasiCell => packetWave xq.2 xq.1)
    packetWave_joint_measurable 32 (by norm_num) (fun x q => packetWave_norm q x)
    (fun x => (Well.w (h • x) : ℂ)) ((scaled_well_integrable hh).ofReal)
    ((Complex.continuous_ofReal.comp (Well.w_contDiff.continuous.comp
      (continuous_const_smul h))).stronglyMeasurable)
    f.val g.val ((Lp.memLp f.val).integrable (by norm_num))
    ((Lp.memLp g.val).integrable (by norm_num))
    (Lp.stronglyMeasurable f.val) (Lp.stronglyMeasurable g.val)

theorem waveGram_aliases {h : ℝ} (hh : 0 < h) (q r : QuasiCell) :
    waveGram h q r = (h^3)⁻¹ • ∑' a : FreeFiber.Alias × FreeFiber.Alias,
      inner ℂ (sectionValue q a.1) (sectionValue r a.2) *
        Well.rawPhysicalFourier Well.w
          (h⁻¹ • (aliasFrequency q.val a.1 - aliasFrequency r.val a.2)) :=
  weighted_blochField_gram hh q.val r.val (sectionValue q) (sectionValue r)
    (sectionValue_fourier_l1 q).1 (sectionValue_fourier_l1 r).1

theorem Qh_embedding_gram {h : ℝ} (hh : 0 < h) (f g : Amplitude) :
    inner ℂ (Qh h (physicalEmbedding f)) (Qh h (physicalEmbedding g)) =
      ∫ q, star (f.val q) * (∫ r, g.val r * waveGram h q r ∂quasiMeasure) ∂quasiMeasure := by
  have hs := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (Qh_selfAdjoint h))
    (physicalEmbedding f) (Qh h (physicalEmbedding g))
  change inner ℂ (Qh h (physicalEmbedding f)) (Qh h (physicalEmbedding g)) =
    inner ℂ (physicalEmbedding f) ((Qh h * Qh h) (physicalEmbedding g)) at hs
  rw [Qh_square] at hs
  exact hs.trans (physicalEmbedding_well_gram hh f g)

#print axioms physicalEmbedding_well_gram
#print axioms Qh_embedding_gram

end Maxwell.Continuum.EffectiveMass
