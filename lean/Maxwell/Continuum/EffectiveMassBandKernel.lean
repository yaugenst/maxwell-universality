import Maxwell.Continuum.EffectiveMassFullKernel
import Maxwell.Continuum.EffectiveMassBandOperator

/-! The exact weak Fourier kernel of the literal physical packet Gram
operator, including the cutoff and every alias pair. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory Auxiliary

def weightedFullAliasKernel (h z : ℝ) (p r : Space) : ℂ :=
  (fourierNormalization : ℂ) * (cutoffBandMultiplier h z p : ℂ) *
    fullAliasKernel h p r * (cutoffBandMultiplier h z r : ℂ)

theorem integral_packetRegion_eq_aliasChart {h : ℝ} (hh : 0 < h)
    (F : Space → ℂ) (hF : ∀ p ∉ aliasChart h, F p = 0) :
    ∫ p in packetRegion h, F p = ∫ p in aliasChart h, F p := by
  rw [← integral_indicator (packetRegion_measurable h),
    ← integral_indicator (aliasChart_measurable h)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p => by
    by_cases hp : p ∈ aliasChart h
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (aliasChart_subset_packetRegion hh hp)]
    · rw [Set.indicator_of_notMem hp]
      by_cases hq : p ∈ packetRegion h
      · rw [Set.indicator_of_mem hq, hF p hp]
      · rw [Set.indicator_of_notMem hq]

theorem bandGramOperator_pairing_full {h z : ℝ} (D : Calibration h z) (f g : ScalarL2) :
    inner ℂ g (bandGramOperator D f) =
      ∫ p in aliasChart h, star (g p) *
        (∫ r in aliasChart h, weightedFullAliasKernel h z p r * f r) := by
  rw [bandGramOperator_pairing]
  change inner ℂ (Qh h (Uh D.h_pos (cutoffAmplitudeOperator D g)))
    (Qh h (Uh D.h_pos (cutoffAmplitudeOperator D f))) = _
  rw [Qh_Uh_full_kernel D.h_pos]
  have hcut : (∫ p in packetRegion h, star (cutoffAmplitudeOperator D g p) *
      ∫ r in packetRegion h, fullAliasKernel h p r * cutoffAmplitudeOperator D f r) =
      ∫ p in packetRegion h, star ((cutoffBandMultiplier h z p : ℂ) * g p) *
        ∫ r in packetRegion h, fullAliasKernel h p r * ((cutoffBandMultiplier h z r : ℂ) * f r) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (cutoffAmplitudeOperator_ae D g)] with p hp
    rw [hp]
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (cutoffAmplitudeOperator_ae D f)] with r hr
    rw [hr]
  rw [hcut]
  rw [integral_packetRegion_eq_aliasChart D.h_pos _ (by
    intro p hp
    simp only [cutoffBandMultiplier_zero_off_chart D.h_pos p hp, Complex.ofReal_zero,
      zero_mul, star_zero])]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p => by
    dsimp only
    rw [integral_packetRegion_eq_aliasChart D.h_pos _ (by
      intro r hr
      simp only [cutoffBandMultiplier_zero_off_chart D.h_pos r hr, Complex.ofReal_zero,
        zero_mul, mul_zero])]
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun r => by
      dsimp only
      have hstar (a : ℝ) : star (a : ℂ) = (a : ℂ) := Complex.conj_ofReal a
      simp only [star_mul, hstar, weightedFullAliasKernel]
      ring

#print axioms bandGramOperator_pairing_full

end Maxwell.Continuum.EffectiveMass
