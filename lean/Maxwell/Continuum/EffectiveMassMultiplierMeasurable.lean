import Maxwell.Continuum.EffectiveMassUniformBounds

/-! Measurability of the literal full Fourier-vector multipliers. Local
holomorphy is used only on the certified chart; the cutoff is exactly zero
outside that chart. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory FreeFiber PeriodicBand Auxiliary

attribute [local irreducible] dielectricBand physicalFiberVector hessianOperator

theorem physicalMomentum_continuous : Continuous physicalMomentum := by
  unfold physicalMomentum realMomentum
  fun_prop

theorem scaledMomentum_mem_physicalChart {h : ℝ} (hh : 0 < h)
    {p : Space} (hp : p ∈ aliasChart h) : physicalMomentum (h • p) ∈ physicalChart := by
  apply small_momentum_mem_physicalChart
  have hn := physicalMomentum_norm_le (h • p)
  rw [scaled_norm hh.le] at hn
  exact hn.trans ((mem_aliasChart hh p).mp hp)

theorem scaledFiber_continuousOn {h : ℝ} (hh : 0 < h) :
    ContinuousOn (scaledFiber h) (aliasChart h) := by
  intro p hp
  have hs : Continuous (fun p : Space => h • p) := by fun_prop
  have hc : Continuous (fun p : Space => physicalMomentum (h • p)) :=
    physicalMomentum_continuous.comp hs
  exact (ContinuousAt.comp (f := fun p : Space => physicalMomentum (h • p))
    (physicalFiberVector_analytic _ (scaledMomentum_mem_physicalChart hh hp)).continuousAt
    hc.continuousAt).continuousWithinAt

theorem bandDenominator_continuousOn {h : ℝ} (hh : 0 < h) (z : ℝ) :
    ContinuousOn (bandDenominator h z) (aliasChart h) := by
  intro p hp
  have hs : Continuous (fun p : Space => h • p) := by fun_prop
  have hc : Continuous (fun p : Space => physicalMomentum (h • p)) :=
    physicalMomentum_continuous.comp hs
  have hb₀ := (ContinuousAt.comp (f := fun p : Space => physicalMomentum (h • p))
    (dielectricBand_analytic _ (scaledMomentum_mem_physicalChart hh hp)).continuousAt
    hc.continuousAt)
  have hb := Complex.continuous_re.continuousAt.comp hb₀
  exact ((hb.sub continuousAt_const).div_const (h^2)).continuousWithinAt

theorem bandMultiplier_continuousOn {h z : ℝ} (D : Calibration h z) :
    ContinuousOn (bandMultiplier h z) (aliasChart h) := by
  apply (bandDenominator_continuousOn D.h_pos z).sqrt.inv₀
  intro p hp
  apply (Real.sqrt_pos.mpr _).ne'
  have ha := bandDenominator_lower D p ((mem_aliasChart D.h_pos p).mp hp)
  have hb := referenceDenominator_ge_one p
  linarith

theorem cutoffBandMultiplier_continuousOn {h z : ℝ} (D : Calibration h z) :
    ContinuousOn (cutoffBandMultiplier h z) (aliasChart h) := by
  have hs : Continuous (fun p : Space => h • p) := by fun_prop
  have hc : Continuous (fun p : Space => Real.sqrt (cutoff (h • p))) :=
    (cutoff_continuous.comp hs).sqrt
  exact hc.continuousOn.mul (bandMultiplier_continuousOn D)

theorem vectorMultiplier_continuousOn {h z : ℝ} (D : Calibration h z) :
    ContinuousOn (vectorMultiplier h z) (aliasChart h) :=
  (Complex.continuous_ofReal.comp_continuousOn (cutoffBandMultiplier_continuousOn D)).smul
    (scaledFiber_continuousOn D.h_pos)

theorem vectorMultiplier_indicator {h z : ℝ} (hh : 0 < h) :
    vectorMultiplier h z = (aliasChart h).indicator (vectorMultiplier h z) := by
  funext p
  by_cases hp : p ∈ aliasChart h
  · exact (Set.indicator_of_mem hp _).symm
  · rw [Set.indicator_of_notMem hp]
    simp only [vectorMultiplier, cutoffBandMultiplier_zero_off_chart hh p hp,
      Complex.ofReal_zero, zero_smul]

theorem vectorMultiplier_measurable {h z : ℝ} (D : Calibration h z) :
    AEStronglyMeasurable (vectorMultiplier h z) (volume : Measure Space) := by
  rw [vectorMultiplier_indicator D.h_pos]
  exact (aestronglyMeasurable_indicator_iff (aliasChart_measurable h)).mpr
    ((vectorMultiplier_continuousOn D).aestronglyMeasurable (aliasChart_measurable h))

theorem referenceMultiplier_continuous : Continuous referenceMultiplier := by
  have hq : Continuous quadratic := continuous_id.inner hessianOperator.continuous
  have hb : Continuous referenceDenominator := continuous_const.add hq
  exact hb.sqrt.inv₀ (fun p => (Real.sqrt_pos.mpr (referenceDenominator_pos p)).ne')

theorem referenceVectorMultiplier_continuous : Continuous referenceVectorMultiplier :=
  (Complex.continuous_ofReal.comp referenceMultiplier_continuous).smul continuous_const

end Maxwell.Continuum.EffectiveMass
