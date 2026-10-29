import Maxwell.Continuum.EffectiveMassAliasSplit
import Maxwell.Continuum.EffectiveMassDiagonalWave
import Maxwell.Continuum.WellFourierTail

/-! Measurability and domination for the literal alias kernels. These
justify subtraction of their weak integral formulas. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory FreeFiber Auxiliary

def weightedAliasTerm (h z : ℝ) (p r : Space) (a : Alias × Alias) : ℂ :=
  (fourierNormalization : ℂ) * inner ℂ (vectorMultiplier h z p a.1)
    (vectorMultiplier h z r a.2) * Well.physicalFourier Well.w (aliasTransfer h p r a.1 a.2)

theorem weightedAliasTerm_eq (h z : ℝ) (p r : Space) (a : Alias × Alias) :
    weightedAliasTerm h z p r a =
      ((fourierNormalization : ℂ) * (cutoffBandMultiplier h z p : ℂ)) *
        (inner ℂ (scaledFiber h p a.1) (scaledFiber h r a.2) *
          Well.physicalFourier Well.w (aliasTransfer h p r a.1 a.2)) *
            (cutoffBandMultiplier h z r : ℂ) := by
  simp only [weightedAliasTerm, vectorMultiplier, lp.coeFn_smul, Pi.smul_apply,
    inner_smul_left, inner_smul_right]
  have hstar (a : ℝ) : (starRingEnd ℂ) (a : ℂ) = (a : ℂ) := Complex.conj_ofReal a
  simp only [hstar]
  ring

theorem weightedAliasTerm_hasSum {h z : ℝ} (D : Calibration h z) (p r : Space) :
    HasSum (weightedAliasTerm h z p r) (weightedFullAliasKernel h z p r) := by
  change HasSum (fun a => weightedAliasTerm h z p r a) _
  by_cases hp : p ∈ aliasChart h
  · by_cases hr : r ∈ aliasChart h
    · have hs := ((fullAliasTerm_summable D.h_pos p r hp hr).hasSum.mul_left
        ((fourierNormalization : ℂ) * (cutoffBandMultiplier h z p : ℂ))).mul_right
          (cutoffBandMultiplier h z r : ℂ)
      simpa only [weightedAliasTerm_eq, weightedFullAliasKernel, fullAliasKernel] using hs
    · simp only [weightedAliasTerm_eq, weightedFullAliasKernel,
        cutoffBandMultiplier_zero_off_chart D.h_pos r hr, Complex.ofReal_zero, mul_zero]
      exact hasSum_zero
  · simp only [weightedAliasTerm_eq, weightedFullAliasKernel,
      cutoffBandMultiplier_zero_off_chart D.h_pos p hp, Complex.ofReal_zero, mul_zero, zero_mul]
    exact hasSum_zero

theorem weightedFullAliasKernel_stronglyMeasurable {h z : ℝ} (D : Calibration h z) :
    StronglyMeasurable (fun pr : Space × Space => weightedFullAliasKernel h z pr.1 pr.2) := by
  apply StronglyMeasurable.hasSum (L := SummationFilter.unconditional (Alias × Alias))
    (f := fun a pr => weightedAliasTerm h z pr.1 pr.2 a)
  · intro a
    have hc (ν : Alias) : StronglyMeasurable (fun p : Space => vectorMultiplier h z p ν) :=
      (lp.evalCLM ℂ (fun _ : Alias => Polarization) 2 ν).continuous.comp_stronglyMeasurable
        (vectorMultiplier_stronglyMeasurable D)
    have ht : Continuous (fun pr : Space × Space =>
        Well.physicalFourier Well.w (aliasTransfer h pr.1 pr.2 a.1 a.2)) := by
      apply (Well.physicalFourier_continuous Well.w Well.w_integrable).comp
      unfold aliasTransfer
      fun_prop
    exact (stronglyMeasurable_const.mul
      ((hc a.1).comp_measurable measurable_fst |>.inner
        ((hc a.2).comp_measurable measurable_snd))).mul ht.stronglyMeasurable
  · intro pr
    exact weightedAliasTerm_hasSum D pr.1 pr.2

theorem diagonalAliasKernel_vector (h z : ℝ) (p r : Space) :
    diagonalAliasKernel h z p r = (fourierNormalization : ℂ) *
      inner ℂ (vectorMultiplier h z p) (vectorMultiplier h z r) * Well.physicalFourier Well.w (p-r) := by
  simp only [diagonalAliasKernel, vectorMultiplier, inner_smul_left, inner_smul_right]
  have hstar (a : ℝ) : (starRingEnd ℂ) (a : ℂ) = (a : ℂ) := Complex.conj_ofReal a
  simp only [hstar]
  ring

theorem diagonalAliasKernel_stronglyMeasurable {h z : ℝ} (D : Calibration h z) :
    StronglyMeasurable (fun pr : Space × Space => diagonalAliasKernel h z pr.1 pr.2) := by
  simp_rw [diagonalAliasKernel_vector]
  exact (stronglyMeasurable_const.mul
    (((vectorMultiplier_stronglyMeasurable D).comp_measurable measurable_fst).inner
      ((vectorMultiplier_stronglyMeasurable D).comp_measurable measurable_snd))).mul
    ((Well.physicalFourier_continuous Well.w Well.w_integrable).comp
      (continuous_fst.sub continuous_snd)).stronglyMeasurable

theorem fourierNormalization_norm_le : ‖(fourierNormalization : ℂ)‖ ≤ 1 := by
  unfold fourierNormalization
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
    (Real.rpow_nonneg (by positivity : 0 ≤ 2 * Real.pi) _)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by norm_num)

theorem fullAliasKernel_bound {h : ℝ} (hh : 0 < h) (p r : Space)
    (hp : p ∈ aliasChart h) (hr : r ∈ aliasChart h) :
    ‖fullAliasKernel h p r‖ ≤ 24576 := by
  have hs := aliasWeight_sum hh.le p r ((mem_aliasChart hh p).mp hp) ((mem_aliasChart hh r).mp hr)
  have hm := tsum_of_norm_bounded (hs.1.hasSum.mul_right 24)
    (fun a => show ‖inner ℂ (scaledFiber h p a.1) (scaledFiber h r a.2) *
      Well.physicalFourier Well.w (aliasTransfer h p r a.1 a.2)‖ ≤ aliasWeight h p r a * 24 by
        rw [norm_mul]
        exact mul_le_mul (norm_inner_le_norm _ _) (well_physicalFourier_le _)
          (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  change ‖fullAliasKernel h p r‖ ≤ (∑' a, aliasWeight h p r a) * 24 at hm
  nlinarith

theorem weightedFullAliasKernel_bound {h z : ℝ} (D : Calibration h z) (p r : Space) :
    ‖weightedFullAliasKernel h z p r‖ ≤ 98304 := by
  by_cases hp : p ∈ aliasChart h
  · by_cases hr : r ∈ aliasChart h
    · rw [weightedFullAliasKernel, norm_mul, norm_mul, norm_mul]
      have hn (a : Space) : ‖(cutoffBandMultiplier h z a : ℂ)‖ = cutoffBandMultiplier h z a := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (cutoffBandMultiplier_nonneg h z a)]
      rw [hn p, hn r]
      calc
        _ ≤ ((1 * 2) * 24576) * 2 :=
          mul_le_mul (mul_le_mul (mul_le_mul fourierNormalization_norm_le
            (cutoffBandMultiplier_le_two D p) (cutoffBandMultiplier_nonneg h z p) (by norm_num))
            (fullAliasKernel_bound D.h_pos p r hp hr) (norm_nonneg _) (by norm_num))
            (cutoffBandMultiplier_le_two D r) (cutoffBandMultiplier_nonneg h z r) (by norm_num)
        _ = _ := by norm_num
    · simp only [weightedFullAliasKernel, cutoffBandMultiplier_zero_off_chart D.h_pos r hr,
        Complex.ofReal_zero, mul_zero, norm_zero]
      norm_num
  · simp only [weightedFullAliasKernel, cutoffBandMultiplier_zero_off_chart D.h_pos p hp,
      Complex.ofReal_zero, mul_zero, zero_mul, norm_zero]
    norm_num

theorem diagonalAliasKernel_bound {h z : ℝ} (D : Calibration h z) (p r : Space) :
    ‖diagonalAliasKernel h z p r‖ ≤ 384 := by
  rw [diagonalAliasKernel_vector, norm_mul, norm_mul]
  have hi := (norm_inner_le_norm (𝕜 := ℂ) (vectorMultiplier h z p) (vectorMultiplier h z r)).trans
    (mul_le_mul (vectorMultiplier_norm_le D p) (vectorMultiplier_norm_le D r)
      (norm_nonneg _) (by norm_num))
  have hb := mul_le_mul (mul_le_mul fourierNormalization_norm_le hi (norm_nonneg _) (by norm_num))
    (well_physicalFourier_le (p-r)) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 * (4*4))
  norm_num at hb ⊢
  exact hb

#print axioms weightedFullAliasKernel_stronglyMeasurable
#print axioms weightedFullAliasKernel_bound

end Maxwell.Continuum.EffectiveMass
