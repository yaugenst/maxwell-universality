import Maxwell.Continuum.WellBump
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! The literal one-dimensional bump and its actual normalization integral. -/

noncomputable section

namespace Maxwell.Continuum.Well

open MeasureTheory Set

def cutoffBase (s : ℝ) : ℝ := expNegInvGlue (1 - 4 * s ^ 2)

theorem cutoffBase_literal (s : ℝ) :
    cutoffBase s = if |s| < 1 / 2 then Real.exp (-1 / (1 - 4 * s ^ 2)) else 0 := by
  by_cases h : |s| < 1 / 2
  · have hs : 0 < 1 - 4 * s ^ 2 := by
      obtain ⟨hl, hu⟩ := abs_lt.mp h
      nlinarith
    rw [ite_eq_left h]
    simp [cutoffBase, expNegInvGlue, hs.not_ge, div_eq_mul_inv]
  · have hs : 1 - 4 * s ^ 2 ≤ 0 := by
      have := le_of_not_gt h
      nlinarith [sq_abs s]
    rw [ite_eq_right h]
    simp [cutoffBase, expNegInvGlue, hs]

theorem cutoffBase_contDiff : ContDiff ℝ (⊤ : ℕ∞) cutoffBase := by
  exact expNegInvGlue.contDiff.comp (by fun_prop)

theorem cutoffBase_nonneg (s : ℝ) : 0 ≤ cutoffBase s := expNegInvGlue.nonneg _

theorem cutoffBase_le_one (s : ℝ) : cutoffBase s ≤ 1 := by
  unfold cutoffBase expNegInvGlue
  split_ifs with hs
  · norm_num
  · rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (inv_nonneg.mpr (le_of_not_ge hs))

theorem cutoffBase_eq_zero_of_half_le (s : ℝ) (hs : 1 / 2 ≤ |s|) : cutoffBase s = 0 := by
  rw [cutoffBase_literal, ite_eq_right (not_lt.mpr hs)]

theorem cutoffBase_support_subset : Function.support cutoffBase ⊆ Icc (-1 / 2 : ℝ) (1 / 2) := by
  intro s hs
  by_contra hout
  have hh : 1 / 2 ≤ |s| := by
    by_contra h
    have hh := abs_lt.mp (lt_of_not_ge h)
    exact hout ⟨by linarith [hh.1], hh.2.le⟩
  exact hs (cutoffBase_eq_zero_of_half_le s hh)

theorem cutoffBase_hasCompactSupport : HasCompactSupport cutoffBase :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc cutoffBase_support_subset

theorem cutoffBase_integrable : Integrable cutoffBase (volume : Measure ℝ) :=
  cutoffBase_contDiff.continuous.integrable_of_hasCompactSupport cutoffBase_hasCompactSupport

theorem exp_four_thirds_lt_four : Real.exp (4 / 3 : ℝ) < 4 := by
  have he : Real.exp 1 < (11 / 4 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hp : Real.exp (4 / 3 : ℝ) ^ 3 = Real.exp 1 ^ 4 := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    norm_num
  have h4 : Real.exp 1 ^ 4 < (11 / 4 : ℝ) ^ 4 := by gcongr
  have h3 : Real.exp (4 / 3 : ℝ) ^ 3 < (4 : ℝ) ^ 3 := by
    rw [hp]
    exact h4.trans (by norm_num)
  exact (pow_lt_pow_iff_left₀ (Real.exp_pos _).le (by norm_num) (by norm_num : (3 : ℕ) ≠ 0)).mp h3

theorem cutoffBase_lower_quarter (s : ℝ) (hs : |s| ≤ 1 / 4) : 1 / 4 ≤ cutoffBase s := by
  obtain ⟨hl, hu⟩ := abs_le.mp hs
  have hd : 3 / 4 ≤ 1 - 4 * s ^ 2 := by nlinarith
  have hd0 : 0 < 1 - 4 * s ^ 2 := by linarith
  have hh : |s| < 1 / 2 := lt_of_le_of_lt hs (by norm_num)
  rw [cutoffBase_literal, ite_eq_left hh]
  have hinv : 1 / (1 - 4 * s ^ 2) ≤ (4 / 3 : ℝ) := by
    apply (div_le_iff₀ hd0).mpr
    nlinarith
  have he := Real.exp_le_exp.mpr (neg_le_neg hinv)
  have hq : (1 / 4 : ℝ) ≤ Real.exp (-(4 / 3 : ℝ)) := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      one_div_le_one_div_of_le (Real.exp_pos _) exp_four_thirds_lt_four.le
  simpa only [neg_div] using hq.trans he

def cutoffNormalization : ℝ := ∫ s, cutoffBase s

theorem cutoffNormalization_bounds : 1 / 8 ≤ cutoffNormalization ∧ cutoffNormalization ≤ 1 := by
  have hi (a b c : ℝ) : Integrable ((Icc a b).indicator (fun _ : ℝ => c)) (volume : Measure ℝ) := by
    exact (integrableOn_const isCompact_Icc.measure_lt_top.ne).integrable_indicator measurableSet_Icc
  constructor
  · have h := integral_mono (hi (-1 / 4) (1 / 4) (1 / 4)) cutoffBase_integrable
      (fun s => show (Icc (-1 / 4 : ℝ) (1 / 4)).indicator (fun _ => (1 / 4 : ℝ)) s ≤ cutoffBase s from by
        by_cases hs : s ∈ Icc (-1 / 4 : ℝ) (1 / 4)
        · rw [indicator_of_mem hs]
          exact cutoffBase_lower_quarter s (abs_le.mpr ⟨by linarith [hs.1], hs.2⟩)
        · rw [indicator_of_notMem hs]
          exact cutoffBase_nonneg s)
    norm_num [integral_indicator_const _ measurableSet_Icc, measureReal_def,
      Real.volume_Icc, smul_eq_mul] at h
    exact h
  · have h := integral_mono cutoffBase_integrable (hi (-1 / 2) (1 / 2) 1)
      (fun s => show cutoffBase s ≤ (Icc (-1 / 2 : ℝ) (1 / 2)).indicator (fun _ => (1 : ℝ)) s from by
        by_cases hs : s ∈ Icc (-1 / 2 : ℝ) (1 / 2)
        · rw [indicator_of_mem hs]
          exact cutoffBase_le_one s
        · rw [indicator_of_notMem hs, Function.notMem_support.mp (fun hm => hs (cutoffBase_support_subset hm))])
    norm_num [integral_indicator_const _ measurableSet_Icc, measureReal_def,
      Real.volume_Icc, smul_eq_mul] at h
    exact h

theorem cutoffNormalization_pos : 0 < cutoffNormalization :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 8) cutoffNormalization_bounds.1

def psi0 (s : ℝ) : ℝ := cutoffBase s / cutoffNormalization

theorem psi0_integrable : Integrable psi0 (volume : Measure ℝ) :=
  cutoffBase_integrable.div_const _

theorem psi0_integral : ∫ s, psi0 s = 1 := by
  change (∫ s, cutoffBase s / cutoffNormalization) = 1
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const]
  change cutoffNormalization * cutoffNormalization⁻¹ = 1
  exact mul_inv_cancel₀ cutoffNormalization_pos.ne'

theorem psi0_nonneg (s : ℝ) : 0 ≤ psi0 s := div_nonneg (cutoffBase_nonneg s) cutoffNormalization_pos.le

theorem psi0_contDiff : ContDiff ℝ (⊤ : ℕ∞) psi0 :=
  cutoffBase_contDiff.div_const _

theorem psi0_support_subset : Function.support psi0 ⊆ Icc (-1 / 2 : ℝ) (1 / 2) := by
  intro s hs
  apply cutoffBase_support_subset
  intro hz
  exact hs (by simp [psi0, hz])

theorem psi0_hasCompactSupport : HasCompactSupport psi0 :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc psi0_support_subset

end Maxwell.Continuum.Well
