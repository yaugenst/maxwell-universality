import Maxwell.Continuum.EffectiveMassPhysicalGram
import Maxwell.Continuum.EffectiveMassScalingPairing
import Maxwell.Continuum.EffectiveMassFiberVariation

/-! Exact angular rescaling of the actual physical well Gram form. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory FreeFiber Bloch BandWavePacket CellBandFourier

def ambientWave (q x : Space) : Polarization :=
  blochField (physicalMomentum q) (PeriodicBand.physicalFiberVector (physicalMomentum q)) x

def ambientGram (h : ℝ) (q r : Space) : ℂ :=
  ∫ x, (Well.w (h • x) : ℂ) * inner ℂ (ambientWave q x) (ambientWave r x)

theorem packetWave_eq_ambient {q : QuasiCell} (hq : q ∈ region) (x : Space) :
    packetWave q x = ambientWave q.val x := by
  rw [packetWave, sectionValue_eq hq]
  rfl

theorem waveGram_eq_ambient {h : ℝ} {q r : QuasiCell} (hq : q ∈ region) (hr : r ∈ region) :
    waveGram h q r = ambientGram h q.val r.val := by
  simp only [waveGram, packetWave_eq_ambient hq, packetWave_eq_ambient hr, ambientGram]

theorem Qh_Uh_quasi_gram {h : ℝ} (hh : 0 < h) (f g : ScalarL2) :
    inner ℂ (Qh h (Uh hh f)) (Qh h (Uh hh g)) =
      ∫ q, star ((scaledAmplitude hh f).val q) *
        (∫ r, (scaledAmplitude hh g).val r * waveGram h q r ∂quasiMeasure) ∂quasiMeasure := by
  change inner ℂ (Qh h (Complex.I • physicalEmbedding (scaledAmplitude hh f)))
    (Qh h (Complex.I • physicalEmbedding (scaledAmplitude hh g))) = _
  rw [map_smul, map_smul, inner_smul_left, inner_smul_right]
  have hI : (starRingEnd ℂ) Complex.I * Complex.I = 1 := by
    rw [starRingEnd_apply, Complex.star_def, Complex.conj_I, neg_mul, Complex.I_mul_I]
    norm_num
  rw [← mul_assoc, hI, one_mul]
  exact Qh_embedding_gram hh _ _

theorem scaledAmplitude_gram_integral {h : ℝ} (hh : 0 < h) (f g : ScalarL2) :
    (∫ q, star ((scaledAmplitude hh f).val q) *
      (∫ r, (scaledAmplitude hh g).val r * waveGram h q r ∂quasiMeasure) ∂quasiMeasure) =
      (amplitudeFactor h : ℂ)^2 * ∫ q : QuasiCell, region.indicator (fun q =>
        ∫ r : QuasiCell, region.indicator (fun r =>
          star (f (h⁻¹ • q.val)) * g (h⁻¹ • r.val) * ambientGram h q.val r.val) r ∂quasiMeasure) q ∂quasiMeasure := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [scaledAmplitude_ae hh f] with q hf
  rw [hf]
  by_cases hq : q ∈ region
  · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq]
    have hi : (∫ r, (scaledAmplitude hh g).val r * waveGram h q r ∂quasiMeasure) =
        (amplitudeFactor h : ℂ) * ∫ r : QuasiCell, region.indicator (fun r =>
          g (h⁻¹ • r.val) * ambientGram h q.val r.val) r ∂quasiMeasure := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [scaledAmplitude_ae hh g] with r hg
      rw [hg]
      by_cases hr : r ∈ region
      · rw [Set.indicator_of_mem hr, Set.indicator_of_mem hr, waveGram_eq_ambient hq hr]
        ring
      · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem hr, zero_mul, mul_zero]
    rw [hi]
    have he : (fun r : QuasiCell => region.indicator (fun r =>
        star (f (h⁻¹ • q.val)) * g (h⁻¹ • r.val) * ambientGram h q.val r.val) r) =
        fun r => star (f (h⁻¹ • q.val)) * region.indicator (fun r =>
          g (h⁻¹ • r.val) * ambientGram h q.val r.val) r := by
      funext r
      by_cases hr : r ∈ region
      · rw [Set.indicator_of_mem hr, Set.indicator_of_mem hr]; ring
      · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem hr, mul_zero]
    rw [he, integral_const_mul]
    have hstar (r : ℝ) : star (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r
    simp only [star_mul, hstar]
    ring
  · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq, star_zero, zero_mul, mul_zero]

theorem Qh_Uh_density_gram {h : ℝ} (hh : 0 < h) (f g : ScalarL2) :
    inner ℂ (Qh h (Uh hh f)) (Qh h (Uh hh g)) =
      (scaledDensity h : ℂ) * ∫ p : Space, (packetRegion h).indicator (fun p =>
        ∫ r : Space, (packetRegion h).indicator (fun r =>
          star (f p) * g r * ambientGram h (h • p) (h • r)) r) p := by
  rw [Qh_Uh_quasi_gram hh, scaledAmplitude_gram_integral hh,
    quasi_double_scaled_integral hh (fun q r =>
      star (f (h⁻¹ • q)) * g (h⁻¹ • r) * ambientGram h q r)]
  have hi (p : Space) : h⁻¹ • (h • p) = p := by
    rw [smul_smul, inv_mul_cancel₀ hh.ne', one_smul]
  simp only [hi, Complex.real_smul, Complex.ofReal_pow]
  have hc : (amplitudeFactor h : ℂ)^2 * (scaledDensity h : ℂ)^2 = (scaledDensity h : ℂ) := by
    have hr : amplitudeFactor h ^ 2 * scaledDensity h ^ 2 = scaledDensity h := by
      calc
        _ = (amplitudeFactor h ^ 2 * scaledDensity h) * scaledDensity h := by ring
        _ = _ := by rw [amplitudeFactor_square hh, one_mul]
    exact_mod_cast hr
  rw [← mul_assoc, hc]

#print axioms Qh_Uh_density_gram

end Maxwell.Continuum.EffectiveMass
