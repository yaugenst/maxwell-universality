import Maxwell.Continuum.WellCutoffBase
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! The literal convolution cutoff, its plateau, and the three-dimensional cutoff. -/

noncomputable section

namespace Maxwell.Continuum.Well

open MeasureTheory Set
open scoped Convolution

def cutoffWindow : ℝ → ℝ := (Icc (-3 / 2 : ℝ) (3 / 2)).indicator (fun _ => 1)

theorem cutoffWindow_integrable : Integrable cutoffWindow (volume : Measure ℝ) := by
  exact (integrableOn_const isCompact_Icc.measure_lt_top.ne).integrable_indicator measurableSet_Icc

theorem cutoffWindow_nonneg (s : ℝ) : 0 ≤ cutoffWindow s := by
  unfold cutoffWindow
  exact indicator_nonneg (fun _ _ => by norm_num) s

theorem cutoffWindow_le_one (s : ℝ) : cutoffWindow s ≤ 1 := by
  unfold cutoffWindow
  by_cases hs : s ∈ Icc (-3 / 2 : ℝ) (3 / 2) <;> simp [hs]

def psi : ℝ → ℝ := cutoffWindow ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] psi0

theorem psi_contDiff : ContDiff ℝ (⊤ : ℕ∞) psi :=
  psi0_hasCompactSupport.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    cutoffWindow_integrable.locallyIntegrable psi0_contDiff

theorem psi_eq_integral (s : ℝ) : psi s = ∫ t, cutoffWindow (s - t) * psi0 t :=
  convolution_mul_swap

theorem psi_integrand_integrable (s : ℝ) :
    Integrable (fun t => cutoffWindow (s - t) * psi0 t) (volume : Measure ℝ) := by
  exact convolutionExistsAt_iff_integrable_swap.mp
    (psi0_hasCompactSupport.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ)
      cutoffWindow_integrable.locallyIntegrable psi0_contDiff.continuous s)

theorem psi_nonneg (s : ℝ) : 0 ≤ psi s := by
  rw [psi_eq_integral]
  exact integral_nonneg (fun t => mul_nonneg (cutoffWindow_nonneg _) (psi0_nonneg t))

theorem psi_le_one (s : ℝ) : psi s ≤ 1 := by
  rw [psi_eq_integral, ← psi0_integral]
  exact integral_mono (psi_integrand_integrable s) psi0_integrable
    (fun t => by nlinarith [cutoffWindow_le_one (s - t), psi0_nonneg t])

theorem psi0_eq_zero_of_half_le (s : ℝ) (hs : 1 / 2 ≤ |s|) : psi0 s = 0 := by
  simp [psi0, cutoffBase_eq_zero_of_half_le s hs]

theorem psi_eq_one (s : ℝ) (hs : |s| ≤ 1) : psi s = 1 := by
  rw [psi_eq_integral, ← psi0_integral]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => by
    by_cases ht : |t| < 1 / 2
    · obtain ⟨hs₁, hs₂⟩ := abs_le.mp hs
      obtain ⟨ht₁, ht₂⟩ := abs_lt.mp ht
      have hmem : s - t ∈ Icc (-3 / 2 : ℝ) (3 / 2) := ⟨by linarith, by linarith⟩
      simp [cutoffWindow, hmem]
    · simp only [psi0_eq_zero_of_half_le t (le_of_not_gt ht), mul_zero])

theorem psi_eq_zero_of_two_le (s : ℝ) (hs : 2 ≤ |s|) : psi s = 0 := by
  rw [psi_eq_integral]
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall (fun t => by
    by_cases ht : |t| < 1 / 2
    · have hnot : s - t ∉ Icc (-3 / 2 : ℝ) (3 / 2) := by
        intro hmem
        obtain ⟨ht₁, ht₂⟩ := abs_lt.mp ht
        have hlt : |s| < 2 := abs_lt.mpr ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
        exact hs.not_gt hlt
      simp [cutoffWindow, hnot]
    · simp only [psi0_eq_zero_of_half_le t (le_of_not_gt ht), mul_zero, Pi.zero_apply])

theorem psi_support_subset : Function.support psi ⊆ Icc (-2 : ℝ) 2 := by
  intro s hs
  have hlt : |s| < 2 := by
    by_contra h
    exact hs (psi_eq_zero_of_two_le s (le_of_not_gt h))
  exact ⟨(abs_lt.mp hlt).1.le, (abs_lt.mp hlt).2.le⟩

theorem psi_hasCompactSupport : HasCompactSupport psi :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc psi_support_subset

theorem psi_integrable : Integrable psi (volume : Measure ℝ) :=
  psi_contDiff.continuous.integrable_of_hasCompactSupport psi_hasCompactSupport

/-- The scalar cutoff in the corner Bloch coordinates, with its literal scale. -/
def chi (q₀ : ℝ) (q : Space) : ℝ := ∏ j : Fin 3, psi (q j / q₀)

theorem chi_nonneg (q₀ : ℝ) (q : Space) : 0 ≤ chi q₀ q :=
  Finset.prod_nonneg (fun _ _ => psi_nonneg _)

theorem chi_le_one (q₀ : ℝ) (q : Space) : chi q₀ q ≤ 1 := by
  exact Finset.prod_le_one₀ (fun _ _ => psi_nonneg _) (fun _ _ => psi_le_one _)

theorem chi_eq_one (q₀ : ℝ) (q : Space) (hq : ∀ j, |q j / q₀| ≤ 1) : chi q₀ q = 1 := by
  exact Finset.prod_eq_one (fun j _ => psi_eq_one _ (hq j))

theorem chi_eq_zero (q₀ : ℝ) (q : Space) (j : Fin 3) (hq : 2 ≤ |q j / q₀|) :
    chi q₀ q = 0 := by
  exact Finset.prod_eq_zero (Finset.mem_univ j) (psi_eq_zero_of_two_le _ hq)

theorem chi_contDiff (q₀ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (chi q₀) := by
  unfold chi
  apply contDiff_prod
  intro j _
  apply psi_contDiff.comp
  exact (PiLp.proj 2 (fun _ : Fin 3 => ℝ) j : Space →L[ℝ] ℝ).contDiff.div_const q₀

end Maxwell.Continuum.Well
