import Maxwell.Continuum.AliasKernelBound
import Maxwell.Continuum.AliasDecayMajorant
import Maxwell.Continuum.EffectiveMassUniformBounds
import Maxwell.Continuum.FiniteSupportKernel

/-! The weighted off-alias kernel and its operator-norm bound. The final
lemma applies to an operator identified with the literal kernel integral. -/

noncomputable section

namespace Maxwell.Continuum.EffectiveMass

open MeasureTheory Auxiliary

def weightedOffAliasKernel (h z : ℝ) (p p' : Space) : ℂ :=
  (2 * Real.pi) ^ (-(3 / 2 : ℝ)) •
    ((cutoffBandMultiplier h z p : ℂ) * offAliasKernel h p p' *
      (cutoffBandMultiplier h z p' : ℂ))

theorem weightedOffAliasKernel_bound {h z : ℝ} (D : Calibration h z)
    (p p' : Space) (hp : p ∈ aliasChart h) (hp' : p' ∈ aliasChart h) :
    ‖weightedOffAliasKernel h z p p'‖ ≤
      (2 : ℝ)^32 * Real.exp (-1 / (512 * Real.sqrt h)) := by
  have hc₀ : 0 ≤ (2 * Real.pi) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (by positivity) _
  have hc₁ : (2 * Real.pi) ^ (-(3 / 2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by norm_num)
  have hk := offAliasKernel_bound D.h_pos p p'
    ((mem_aliasChart D.h_pos p).mp hp) ((mem_aliasChart D.h_pos p').mp hp')
  have hs := cutoffBandMultiplier_le_two D p
  have hs' := cutoffBandMultiplier_le_two D p'
  rw [weightedOffAliasKernel, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc₀,
    norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (cutoffBandMultiplier_nonneg h z p),
    abs_of_nonneg (cutoffBandMultiplier_nonneg h z p')]
  calc
    _ ≤ 1 * ((2 * ((2 : ℝ)^30 * Real.exp (-1 / (512 * Real.sqrt h)))) * 2) :=
      mul_le_mul hc₁ (mul_le_mul
        (mul_le_mul hs hk (norm_nonneg _) (by norm_num)) hs'
        (cutoffBandMultiplier_nonneg h z p') (by positivity))
        (mul_nonneg (mul_nonneg (cutoffBandMultiplier_nonneg h z p) (norm_nonneg _))
          (cutoffBandMultiplier_nonneg h z p')) (by norm_num)
    _ = _ := by ring

theorem weightedOffAliasKernel_zero_left {h z : ℝ} (hh : 0 < h)
    (p p' : Space) (hp : p ∉ aliasChart h) : weightedOffAliasKernel h z p p' = 0 := by
  simp only [weightedOffAliasKernel, cutoffBandMultiplier_zero_off_chart hh p hp,
    Complex.ofReal_zero, zero_mul, smul_zero]

theorem weightedOffAliasKernel_zero_right {h z : ℝ} (hh : 0 < h)
    (p p' : Space) (hp' : p' ∉ aliasChart h) : weightedOffAliasKernel h z p p' = 0 := by
  simp only [weightedOffAliasKernel, cutoffBandMultiplier_zero_off_chart hh p' hp',
    Complex.ofReal_zero, mul_zero, smul_zero]

theorem alias_measure_majorant {h : ℝ} (hh : 0 < h) :
    ((2 : ℝ)^32 * Real.exp (-1 / (512 * Real.sqrt h))) *
      volume.real (aliasChart h) ≤ (2 : ℝ)^512 * h := by
  calc
    _ ≤ ((2 : ℝ)^32 * Real.exp (-1 / (512 * Real.sqrt h))) * (h⁻¹)^3 :=
      mul_le_mul_of_nonneg_left (aliasChart_volume hh) (by positivity)
    _ ≤ (2 : ℝ)^100 * (h⁻¹)^3 * Real.exp (-1 / (512 * Real.sqrt h)) := by
      have hc := mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ)^32 ≤ (2 : ℝ)^100)
        (show 0 ≤ (h⁻¹)^3 * Real.exp (-1 / (512 * Real.sqrt h)) by positivity)
      nlinarith
    _ ≤ (2 : ℝ)^512 * h := alias_decay_majorant hh

theorem weightedOffAlias_operator_norm {h z : ℝ} (D : Calibration h z)
    (T : ScalarL2 →L[ℂ] ScalarL2)
    (hT : ∀ f : ScalarL2, T f =ᵐ[volume]
      (aliasChart h).indicator (fun p =>
        ∫ p' in aliasChart h, weightedOffAliasKernel h z p p' * f p')) :
    ‖T‖ ≤ (2 : ℝ)^512 * h := by
  have hn := KernelIntegral.finite_support_operator_norm
    (aliasChart_measurable h) (aliasChart_finite h) T (weightedOffAliasKernel h z)
    (by positivity : 0 ≤ (2 : ℝ)^32 * Real.exp (-1 / (512 * Real.sqrt h)))
    (fun p hp p' hp' => weightedOffAliasKernel_bound D p p' hp hp') hT
  exact hn.trans (alias_measure_majorant D.h_pos)

end Maxwell.Continuum.EffectiveMass
