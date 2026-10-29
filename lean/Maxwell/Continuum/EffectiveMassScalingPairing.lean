import Maxwell.Continuum.EffectiveMassScalingIntegral

/-! Two exact momentum changes of variables for a packet Gram form. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory Bloch BandWavePacket

theorem quasi_double_scaled_integral {h : ℝ} (hh : 0 < h) (F : Space → Space → ℂ) :
    (∫ q : QuasiCell, region.indicator (fun q =>
      ∫ r : QuasiCell, region.indicator (fun r => F q.val r.val) r ∂quasiMeasure) q ∂quasiMeasure) =
      (scaledDensity h)^2 • ∫ p : Space, (packetRegion h).indicator (fun p =>
        ∫ r : Space, (packetRegion h).indicator (fun r => F (h • p) (h • r)) r) p := by
  have heq : (fun q : QuasiCell => region.indicator (fun q =>
      ∫ r : QuasiCell, region.indicator (fun r => F q.val r.val) r ∂quasiMeasure) q) =
      fun q : QuasiCell => (scaledDensity h : ℂ) * region.indicator (fun q =>
        ∫ r : Space, (packetRegion h).indicator (fun r => F q.val (h • r)) r) q := by
    funext q
    by_cases hq : q ∈ region
    · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq,
        quasi_scaled_chart_integral hh]
      rfl
    · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq, mul_zero]
  rw [heq, integral_const_mul,
    quasi_scaled_chart_integral hh (fun q => ∫ r : Space,
      (packetRegion h).indicator (fun r => F q (h • r)) r)]
  simp only [Complex.real_smul, Complex.ofReal_pow]
  ring

#print axioms quasi_double_scaled_integral

end Maxwell.Continuum.EffectiveMass
