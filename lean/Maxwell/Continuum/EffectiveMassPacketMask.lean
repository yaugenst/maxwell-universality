import Maxwell.Continuum.EffectiveMassFullKernel
import Maxwell.Continuum.EffectiveMassReferenceScalar

/-! The literal chart projection on scalar momentum L² and the small
reference-multiplier tail outside that chart. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory Auxiliary

def packetProfile (h : ℝ) : Well.UnitProfile where
  coefficient := (packetRegion h).indicator (fun _ => 1)
  measurable := measurable_const.indicator (packetRegion_measurable h)
  nonneg p := by
    by_cases hp : p ∈ packetRegion h
    · rw [Set.indicator_of_mem hp]; norm_num
    · rw [Set.indicator_of_notMem hp]
  le_one p := by
    by_cases hp : p ∈ packetRegion h
    · rw [Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem hp]; norm_num

def packetMask (h : ℝ) : ScalarL2 →L[ℂ] ScalarL2 := (packetProfile h).multiplier

theorem packetMask_ae (h : ℝ) (f : ScalarL2) :
    packetMask h f =ᵐ[volume] (packetRegion h).indicator f := by
  filter_upwards [(packetProfile h).multiplier_ae f] with p hp
  change (packetProfile h).multiplier f p = _
  rw [hp]
  change (((packetRegion h).indicator (fun _ => (1 : ℝ)) p : ℝ) : ℂ) * f p = _
  by_cases hq : p ∈ packetRegion h
  · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq, Complex.ofReal_one, one_mul]
  · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq, Complex.ofReal_zero, zero_mul]

theorem referenceMultiplier_outside_packet {h z : ℝ} (D : Calibration h z)
    (p : Space) (hp : p ∉ packetRegion h) : referenceMultiplier p ≤ (2 : ℝ)^91 * h := by
  apply referenceMultiplier_tail D p
  intro hc
  have hn := cutoff_ne_zero_norm_le (show cutoff (h • p) ≠ 0 by rw [hc]; norm_num)
  rw [scaled_norm D.h_pos.le] at hn
  exact hp (aliasChart_subset_packetRegion D.h_pos ((mem_aliasChart D.h_pos p).mpr hn))

def packetReferenceTail (h : ℝ) : ScalarL2 →L[ℂ] ScalarL2 :=
  (1 - packetMask h).comp referenceScalarOperator

theorem packetReferenceTail_norm {h z : ℝ} (D : Calibration h z) :
    ‖packetReferenceTail h‖ ≤ (2 : ℝ)^91 * h := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (by positivity) D.h_pos.le)
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  have he : packetReferenceTail h f = referenceScalarOperator f - packetMask h (referenceScalarOperator f) := rfl
  rw [he]
  filter_upwards [Lp.coeFn_sub (referenceScalarOperator f) (packetMask h (referenceScalarOperator f)),
    packetMask_ae h (referenceScalarOperator f), referenceScalarOperator_ae f] with p hsub hm hs
  rw [hsub, Pi.sub_apply, hm]
  by_cases hp : p ∈ packetRegion h
  · rw [Set.indicator_of_mem hp, sub_self, norm_zero]
    exact mul_nonneg (mul_nonneg (by positivity) D.h_pos.le) (norm_nonneg _)
  · rw [Set.indicator_of_notMem hp, sub_zero, hs, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (referenceMultiplier_nonneg p)]
    exact mul_le_mul_of_nonneg_right (referenceMultiplier_outside_packet D p hp) (norm_nonneg _)

end Maxwell.Continuum.EffectiveMass
