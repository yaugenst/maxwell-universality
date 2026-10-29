import Maxwell.Continuum.EffectiveMassScaledGram
import Maxwell.Continuum.EffectiveMassMultiplierMeasurable

/-! The complete, literal alias-pair kernel of the scaled physical
packet Gram form. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory FreeFiber PeriodicBand Bloch BandWavePacket

theorem ambientRegion_isOpen : IsOpen ambientRegion := by
  apply chart_isOpen.preimage
  change Continuous (fun q : Space => unscale (physicalMomentum q))
  unfold unscale
  exact (continuous_const : Continuous (fun _ : Space =>
    (backgroundAmplitude : ℂ)⁻¹)).smul physicalMomentum_continuous

theorem packetRegion_measurable (h : ℝ) : MeasurableSet (packetRegion h) :=
  (quasiCell_measurable.inter ambientRegion_isOpen.measurableSet).preimage (measurable_const_smul h)

theorem aliasChart_subset_packetRegion {h : ℝ} (hh : 0 < h) : aliasChart h ⊆ packetRegion h := by
  intro p hp
  have hnorm : ‖h • p‖ ≤ 4 * smallRadius := by
    rw [scaled_norm hh.le]
    exact (mem_aliasChart hh p).mp hp
  have hsmall : 4 * smallRadius < Real.pi / 2 := by
    have hs : 4 * smallRadius ≤ (1 : ℝ) / 2 := by norm_num [smallRadius, backgroundAmplitude]
    linarith [Real.pi_gt_three]
  refine ⟨?_, unscale_mem_chart (scaledMomentum_mem_physicalChart hh hp)⟩
  intro j
  have hj : |(h • p) j| < Real.pi / 2 := by
    exact (show |(h • p) j| ≤ ‖h • p‖ from PiLp.norm_apply_le (h • p) j).trans_lt
      (hnorm.trans_lt hsmall)
  have hb := abs_lt.mp hj
  exact ⟨by simpa only [neg_div] using hb.1.le, hb.2⟩

theorem scaledFiber_l1_of_packetRegion {h : ℝ} {p : Space} (hp : p ∈ packetRegion h) :
    Summable (fun ν => ‖scaledFiber h p ν‖) ∧ ∑' ν, ‖scaledFiber h p ν‖ ≤ 32 :=
  FiberNormalization.normalizedFiberVector_fourier_l1 hp.2

def fullAliasKernel (h : ℝ) (p r : Space) : ℂ :=
  ∑' a : FreeFiber.Alias × FreeFiber.Alias,
    inner ℂ (scaledFiber h p a.1) (scaledFiber h r a.2) *
      Well.physicalFourier Well.w (aliasTransfer h p r a.1 a.2)

theorem density_ambientGram {h : ℝ} (hh : 0 < h) {p r : Space}
    (hp : p ∈ packetRegion h) (hr : r ∈ packetRegion h) :
    (scaledDensity h : ℂ) * ambientGram h (h • p) (h • r) =
      (fourierNormalization : ℂ) * fullAliasKernel h p r := by
  have he := normalized_blochField_gram hh p r (scaledFiber h p) (scaledFiber h r)
    (scaledFiber_l1_of_packetRegion hp).1 (scaledFiber_l1_of_packetRegion hr).1
  rw [fourierNormalization_square, mul_comm (h^3)] at he
  exact he

theorem Qh_Uh_full_kernel {h : ℝ} (hh : 0 < h) (f g : ScalarL2) :
    inner ℂ (Qh h (Uh hh f)) (Qh h (Uh hh g)) =
      (fourierNormalization : ℂ) * ∫ p in packetRegion h,
        star (f p) * (∫ r in packetRegion h, fullAliasKernel h p r * g r) := by
  rw [Qh_Uh_density_gram hh, ← integral_indicator (packetRegion_measurable h)]
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p => by
    dsimp only
    by_cases hp : p ∈ packetRegion h
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp,
        ← integral_indicator (packetRegion_measurable h),
        ← integral_const_mul, ← integral_const_mul, ← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun r => by
        dsimp only
        by_cases hr : r ∈ packetRegion h
        · rw [Set.indicator_of_mem hr, Set.indicator_of_mem hr]
          have he := density_ambientGram hh hp hr
          calc
            _ = star (f p) * g r * ((scaledDensity h : ℂ) * ambientGram h (h • p) (h • r)) := by ring
            _ = _ := by rw [he]; ring
        · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem hr]
          ring
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]
      ring

#print axioms Qh_Uh_full_kernel

end Maxwell.Continuum.EffectiveMass
