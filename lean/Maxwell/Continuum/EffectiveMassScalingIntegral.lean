import Maxwell.Continuum.EffectiveMassScalingPacket
import Maxwell.Continuum.EffectiveMassKernelGram

/-! Exact change of variables for scalar integrals on the constructed
band chart, with the quasi-cell Jacobian retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory Bloch BandWavePacket PeriodicBand

def ambientRegion : Set Space := {q | unscale (physicalMomentum q) ∈ chart}

def packetRegion (h : ℝ) : Set Space :=
  {p | h • p ∈ quasiCell ∩ ambientRegion}

theorem region_iff_ambient (q : QuasiCell) : q ∈ region ↔ q.val ∈ ambientRegion := Iff.rfl

theorem fourierNormalization_square : fourierNormalization^2 = angularDensity := by
  unfold fourierNormalization angularDensity
  rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ 2 * Real.pi)]
  norm_num

theorem quasi_chart_integral (g : Space → ℂ) :
    (∫ q : QuasiCell, region.indicator (fun q => g q.val) q ∂quasiMeasure) =
      angularDensity • ∫ q : Space, (quasiCell ∩ ambientRegion).indicator g q := by
  have heq : region.indicator (fun q : QuasiCell => g q.val) =
      fun q => ambientRegion.indicator g q.val := by
    funext q
    by_cases hq : q ∈ region
    · rw [Set.indicator_of_mem hq, Set.indicator_of_mem ((region_iff_ambient q).mp hq)]
    · rw [Set.indicator_of_notMem hq,
        Set.indicator_of_notMem (mt (region_iff_ambient q).mpr hq)]
  rw [heq, quasiMeasure, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ ((2 * Real.pi)^3)⁻¹),
    integral_subtype_comap quasiCell_measurable,
    ← integral_indicator quasiCell_measurable]
  rw [Set.indicator_indicator]
  rfl

theorem quasi_scaled_chart_integral {h : ℝ} (hh : 0 < h) (g : Space → ℂ) :
    (∫ q : QuasiCell, region.indicator (fun q => g q.val) q ∂quasiMeasure) =
      scaledDensity h • ∫ p : Space, (packetRegion h).indicator (fun p => g (h • p)) p := by
  rw [quasi_chart_integral]
  have hc := Measure.integral_comp_smul_of_nonneg (volume : Measure Space)
    ((quasiCell ∩ ambientRegion).indicator g) h (hR := hh.le)
  rw [show Module.finrank ℝ Space = 3 from finrank_euclideanSpace_fin] at hc
  have heq : (fun p => (quasiCell ∩ ambientRegion).indicator g (h • p)) =
      (packetRegion h).indicator (fun p => g (h • p)) := by
    funext p
    by_cases hp : h • p ∈ quasiCell ∩ ambientRegion
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (show p ∈ packetRegion h from hp)]
    · rw [Set.indicator_of_notMem hp,
        Set.indicator_of_notMem (show p ∉ packetRegion h from hp)]
  rw [heq] at hc
  rw [hc, scaledDensity, smul_smul, mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero 3 hh.ne'), mul_one]

#print axioms fourierNormalization_square
#print axioms quasi_scaled_chart_integral

end Maxwell.Continuum.EffectiveMass
